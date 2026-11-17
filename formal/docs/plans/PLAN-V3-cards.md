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

> **D-P71 reading rule for the M0–M4 cards (added by PL.G, 2026-11-17).** These cards were written
> when the goal was a headline at fixture F1, and their text is otherwise unchanged. Read them so:
> - "at the deployment", "at F1", "at `poseidonRender`" in a KAT, PROBE, gate or exporter card is a
>   **test** (a W12 witness or falsifier, a W14 run, the reference or artifact gate). It stays.
> - A deliverable that **states or proves a headline or a block row at a fixture** is void. Three
>   places: REF.6's `lowering_equivalence_poseidon_at` (do not state it; `poseidonRenderAt s` and
>   `SrsEncodes s` are still delivered, as test data); ST.5's and DG.1's use of
>   `lowering_equivalence_poseidon` as the cone root (the root is `lowering_correct` once ST.1 has
>   landed `GeneratorTheorem.lean`; until then report the cone of `lowering_equivalenceV3_of`).
> - Where a card says "Sonnet-only split", "ROW.x.n" or "children", and the child has no card yet,
>   the parent SKELETON card issues it (EXECUTION-V2 §4): it is not READY before the parent merges.

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

GEN · PORT · box 2.5 h · Sonnet · after ST.4, RECON.1

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

INFRA · SKELETON · box 2.5 h · strongest · after SIM.1, RECON.2

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

### SIM.6 — The prefix rows: prefix_sim and prefix_prog [D-P71: RESTATED]

SEM · PROOF · box 2.5 h · strongest · after SIM.2, RECON.2, OBJ.4, SIM.6.a–d, RECON.3

- **Goal.** For every valid render: from an entry frame, every run of the code before the first
  slice reverts or ends at `StageInv .start`; under honest calls and accepted calldata a run exists.
- **Needs.** `SoundnessV3.lean`: `prefix_sim` (:772), `prefix_prog` (:1170), `preBlock` (:736),
  `StageInv`, `BaseInv`. `GeneratorRows.lean` §4: `model_flags_of_valid`, `layout_static_of_valid`,
  `abi_guard_sem`, `funDefs_noop`, `helpers_funDefs` (proved). `Program.lean:66-116`;
  `Blocks.lean:191-198`. Premise gaps PG-NOSHADOW, PG-FRMOD, PG-G1ID, `NUM_INSTANCE_CPTR` and
  `TRANSCRIPT_MPTR` of PG-CONSTS-TP: supplied by `ValidV3` after RECON.1 and OBJ.4.
- **Does NOT need.** A snapshot, `LeanAccepts` (for `prefix_sim`), a fixture, `native_decide`, loops.
- **VERIFY FIRST.** `check.sh soundness`; the four children are closed; `Frame` has `cdSize`.
- **Do.**
  1. `preSlice` in statement-list form: `model_flags_of_valid` makes `wrapperLocals` the single
     `let vk`; push the inliner through the three groups with `inlineScan_append` (GEN.4).
  2. ABI guard: `abi_guard_sem`. Memory guard: reverts, or passes (`EntryFrame.fmp`).
  3. Helpers: `funDefs_noop` with `helpers_funDefs`. `let r`, `let success := true`: two steps.
  4. Assemble `StageInv .start`: `Frame` from `DeploymentV2`, `EntryFrame.shape` and the two lets;
     `BaseInv .start` from `EntryFrame.zeroAbove` with PG-G1ID and from PG-FRMOD (`LocalsOk`);
     `LeanRaw .start` is `abi_guard_sem`'s conclusion; `Mirror .start` and `Agree .start` are
     immediate (`leanStage … .start = .ok witnessSnapshot`).
  5. `prefix_prog`: exhibit the run; `LeanAccepts` passes the ABI guard (decode guards 1–4).
- **Deliverable.** `prefix_sim`, `prefix_prog` as stated in `SoundnessV3.lean`, sorry-free, for every
  `R`.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.prefix_sim [propext, Classical.choice,
  Quot.sound] native []`, the same for `prefix_prog`; falsifier: with `abiHeadOk` replaced by
  `envelopeOk` in `LeanRaw .start` the proof fails (record the goal).
- **Stop if.** `Agree .start` needs `Inv .start` at a snapshot other than `witnessSnapshot` for a
  decoding (then `BaseInv`'s reading of `Inv .start` is wrong: report).
- **Guidance.** A test, not a proof: one `example` instantiating both at `poseidonRender` once
  `ValidV3` is inhabited there.

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

> **D-P71: OPTIONAL — off the path.** This probe measures the kernel cost of UNROLLED loops on a literal slice. Under D-P71 loops are not unrolled (GEN.3's invariant rule) and no proof is on a literal slice, so nothing depends on this card. Run it only if a row card reports that the kernel cost of one loop ITERATION or of a long straight-line group is the obstacle.


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

> **D-P71 addition.** Also prove `wpSS_exists_C` (the liveness form with call summaries: statement, `CLive` and `Cfail_live` in `prooftech/VKP.lean`, landed by GEN.0). `wpSS_exists` alone cannot be used once a helper is summarised, which is always the case when the scope is a variable; GEN.1 and every progress row use the `_C` form. Run the existence half at the honest dialect (`Bfun`). This card is therefore after T3.1b and GEN.0.


SEM · PROOF · box 2.5 h · strongest · after T3.1b, GEN.0

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

### T3.3 — Generated slice literals with pins [D-P71: TEST ONLY]

> **D-P71.** Kept as a test: the literal slices feed the W14 run-it gate (T3.11). No proof may depend on a literal slice or its `native_decide` pin.


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

### T3.4 — TraceReturn at the deployment (calibration A) [D-P71: DROPPED]

> **D-P71.** Not run. The TraceReturn row is proved for every render (`tr_blockSound`, `tr_blockProgress`); SIM.7 migrates it to `BlockSim`.


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

### T3.6 — vkLoading row at the deployment (calibration B) [D-P71: REPLACED BY GEN.1]

> **D-P71.** Not run. GEN.1 proves the vkLoading row for every render.


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

> **D-P71: DROPPED.** Its deliverable `lag_runs_dep` is a proof on the literal lagrange slice of the fixture. The lagrange row is proved for every render by T3.9 and its children, with GEN.3's loop rule; the cut rule `allRuns_cons_wp` it would have exercised is already in the engine.


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

### T3.9 — Lagrange row for every render (calibration C) [D-P71: RESTATED]

SEM · PROOF · box 2.5 h · strongest · after GEN.1, GEN.3, HLP.1.c, T3.8, OBJ.4, T3.9.a–h, RECON.3

- **Goal.** `lag_blockSim` and `lag_blockProgS` for every `R`, from the children. This is the first
  row with loops and a demonic `staticcall`; its measured cost prices everything after it.
- **Needs.** `GeneratorRows.lean` §5: `lag_slice`, `lagInner`, `lagInner_length`, the five loop
  lemmas, `LagWords`, `LagRel`, `lag_agrees`, `lag_poison`, `lag_blockSim`, `lag_blockProgS`;
  `batch_invert_summary`. Emitter `GenAst.lean:681-761`. `SoundnessV3.lean`: `StageInv`, `leanStage`
  (:336), `agree_of_one` (:1259). `Inv.lean:725` (`InvAt`, the `.lagrange` clauses :779-787).
  Premise gaps PG-NOSHADOW, PG-CONSTS-LAG, PG-FRMOD, PG-NEGLAG.
- **Does NOT need.** A fixture, literal slices, `native_decide`, PCS, the quotient.
- **VERIFY FIRST.** `check.sh soundness`; children closed; `GeneratorRowsWitness.lean` still prints
  `lagChildrenHyps = true` and `(6, 1, 9, some 10688, some 26560, some 4452)`.
- **Do.**
  1. T3.9.f (in this card): the fixed-text statements between the loops and the nine tail
     statements, by GEN.0's parametric execution; the result is a `StmtsContractAll` for the whole
     inner block with post `∃ W, LagRel … W ∧ <six slots hold W's words> ∧ <memory outside the
     denominators window, the scratch window and the six slots unchanged>`.
  2. Last statement: with `success = 1` it is skipped; with `success = 0` it reverts.
  3. `StageInv .lagrange` from the post: `Frame` and `Mirror` by the unchanged-memory conjunct and
     layout disjointness; `Agree .lagrange` for each decoding by `lag_agrees` (take `S` from
     `Agree .transcript`, `x` and `ω`-words from `Inv .transcript`/`Inv .vk`).
  4. `lag_blockSim` = step 3 and `lag_poison`. `lag_blockProgS`: exhibit the run; `CompleteSide`
     gives `xⁿ ≠ 1` and `x ≠ ωⁱ`, so `batch_invert` returns `ret = 1`.
  5. Report: lines per statement, elaboration and kernel seconds, hours, per child.
- **Deliverable.** `theorem lag_blockSim (R) (product) (hR : R.Valid) (hpins : SimPins R) (hpc) (H)
  (vkAddr) (cd) (g) : BlockSim R Partial.lagrange H vkAddr (permissive (callsOf product)) g cd` and
  `lag_blockProgS`, sorry-free.
- **Accept.** `#assert_axioms` on both with `[propext, Classical.choice, Quot.sound] native []`;
  `#cone_sorries lag_blockSim` is 0; no `maxHeartbeats`, no `maxRecDepth` raise; kernel ≤ 60 s for
  the file.
- **Stop if.** `2 ≤ R.pv.numNegLagranges` is not derivable from `hR` (PG-NEGLAG): do not add it;
  write the render with `numNegLagranges = 1` and the two values that differ, and ask the human. A
  missed Accept line goes to the human (D-P71): the per-fixture row is not a fallback.
- **Guidance.** The layout disjointness facts step 3 needs (denominators window against the six
  slots, the VK payload and the `g1_identity` window) come from `memory.map.WellFormed` through
  OBJ.4's `expectedConsts`; list every one used in the report. Sonnet-only split: step 1 by
  statement group (0–2, 4–6, 8–12, 14–17, 19–27) / step 2 / step 3 per `StageInv` component / step 4.

### T3.10 — Quotient numerator: route B only [D-P71: RESTATED]

> **D-P72 constraint (M9).** State the contract `QInterpRefines` over (a) a **memory window** (base address and length as parameters; the verifier's slice is the instance at the plan view's quotient frame) and (b) a **dialect parameter** (not fixed to `Bridge.Dialect c g`), so that the same theorem serves the embedded numerator and the external evaluator's body, which runs in the closed dialect on the callee's copy of the frame (WID.17). The agreement relation is over offsets within the window, not plan-view addresses.


SEM · STATEMENT · box 2.5 h · strongest · after OBJ.2, OBJ.14, OBJ.15

- **Goal.** A typechecked contract for the interpreter loop of the numerator block as an emitter
  prints it, for every program, with witness and falsifier. Route A is excluded by D-P71.
- **Needs.** `GeneratorRows.lean` §7: `QInterpRefines` (the contract shape, parametric in the
  emitted block), `qlin_slice`, `qlinInner`. `Generator/Quotient/VmReference.lean:902`
  (`evalQuotientIdentity`); `Lowering/Qvm.lean:189-214` (`Valuation`, `evalExprρ`, `memOfρ`);
  OBJ.15's `emitQuotientNumeratorA`; `Generator/LoweringPlan.lean:392-420` (`QuotientReadModel`).
- **Does NOT need.** A fixture; the builder sorries (they are ROW.Q's children, not this card's).
- **VERIFY FIRST.** OBJ.15's emitter exists and its `stmtsBeq` gate against the parse is green at F1
  and at the all-arms context. If it does not exist: STOP (PG-Q-OBJECT).
- **Do.**
  1. Name the interpreter's state in the Yul environment: program counter, stack pointer, the
     program and constant windows. Define `AtSegment`, `Top`, `Agrees` (the frame valuation) as
     `def`s over `PlanView` addresses.
  2. Instantiate `QInterpRefines` at the emitter's loop and those three predicates: this is the
     contract.
  3. Classify the opcode arms of the emitter into families with one shared proof shape each.
  4. Witness: at F1, the instance's hypotheses hold for the first identity segment (`#eval`).
     Falsifier: one opcode arm's operand width changed in the emitter makes the conclusion false on
     that segment (`#eval` of the fuel interpreter).
- **Deliverable.** The three predicates, the contract statement (a sorry), the arm table, witness
  and falsifier.
- **Accept.** The statement typechecks under `check.sh soundness`; `#assert_axioms` on the witness
  lemma with `[propext, Classical.choice, Quot.sound] native []` if it is a theorem (an `#eval`
  witness is recorded as a test).
- **Stop if.** The interpreter reads a memory window `QuotientReadModel` does not describe: that is
  a finding about the generator; report the opcode and the address.
- **Guidance.** The loop's guard and `switch` read memory: it is the one loop of the program whose
  bound is not a layout numeral. Its termination measure is the program counter against the program
  length word. Sonnet-only split: step 1 / 2 / 3 / 4.

### T3.11 — Executable exhibit as a KAT [D-P71: TEST ONLY]

> **D-P71.** Kept as a test: it is the W14 exhibit. It is never a premise of a proof.


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

> **Re-measured at `aeba06b` (dry run of the orchestrator):** the sorry register is already in sync
> (F.1 regenerated it), and `kat_gate.py` has no `--static` mode. This card is therefore the two
> annotation fixes and the pin, as in `QUEUE.md`. Adding `--static` is DG.2's business, not this
> card's.

- **Goal.** `bash scripts/checks.sh` exits 0 at the tip, with no new tooling.
- **Needs.** `scripts/kat_gate.py:113` (`EXPECTED_KAT_TOTAL = 1393`; measured 1397 since `2041977`);
  `Midfall/Instances/DeployedProfile.lean:857` and `Midfall/Instances/PoseidonCoherence.lean:502`
  (annotations `-- expect TRUE`; the gate compares case-sensitively and the values print `true`).
  Evidence area: `bash docs/plans/V3-evidence/check.sh probes`.
- **Does NOT need.** Any new gate or script, any change to `checks.sh`, any re-hash of a frozen
  file, any PLAN-V3 decision.
- **Do.**
  1. `python3 scripts/kat_gate.py` — fails in about a second on the total (records the number).
  2. Correct the two annotations to `-- expect true`, keeping the prose after them.
  3. Move `EXPECTED_KAT_TOTAL` (and `EXPECTED_KAT_FILES` if it moved) to the measured values; name
     in the commit the commit that added the four gates (`2041977`).
  4. One full `python3 scripts/kat_gate.py` run, then `bash scripts/checks.sh` once.
- **Deliverable.** One commit touching exactly `scripts/kat_gate.py` and the two `.lean` files.
- **Accept.** `bash scripts/checks.sh` exits 0, and its KAT line names 1397 checks compared (or the
  re-measured total). Falsifier: with one annotation restored to `expect TRUE`, `kat_gate.py`
  fails naming that file.
- **Stop if.** Any gate other than these is red once the total is right: report its first failing
  line and do not adjust its expectation.
- **Guidance.** The full KAT pass takes about 8 minutes (102 files). Caught: REVIEW-V3 RV-40.

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

### DG.4 — State `Done` for the generator theorem, with its refutation [D-P71: RESTATED]

INFRA · STATEMENT · box 2 h · Sonnet · after DG.1, ST.1, REF.8

- **Goal.** DONE is one Lean proposition with no fixture in its headline, landed together with the
  theorem that says it does not hold today.
- **Needs.** `docs/plans/V3-evidence/lean/statements/GeneratorTheorem.lean` §3 (`GateAtV3`,
  `hypothesesInhabitedV3_of_gateAtV3`, `GeneratorDone`, `GeneratorDone.returns`);
  `lean/tooling/T7.lean` (`ArtifactEq` :737 and the V2-shaped `Done`, for the three fixture
  fields); the module ST.1 landed.
- **Does NOT need.** A proof of any field; the fixture calldata term (it is a parameter).
- **VERIFY FIRST.** `bash docs/plans/V3-evidence/check.sh statements` and `tooling` pass.
- **Do.**
  1. Port `GateAtV3`, `hypothesesInhabitedV3_of_gateAtV3`, `GeneratorDone` and
     `GeneratorDone.returns` verbatim.
  2. In `Midfall/Instances/GeneratorDone.lean` define
     `structure Done (cd : Bytes) : Prop` with fields
     `proof : GeneratorDone poseidonRender cd`, `reference : nativeReplay_ok = true` (REF.8's
     `Midfall.Instances.NativeReplay.nativeReplay_ok`),
     `artifact : ArtifactEq poseidonRender.model poseidonVerifierDump`,
     `vkArtifact : renderHalo2VerifyingKey poseidonRender.plan.vk = poseidonVkDump`.
  3. Prove `not_done_today (cd) : ¬ Done cd` from `¬ ValidV3 poseidonRender`
     (`StatementsV3Deploy.lean: poseidon_payloadAgrees_not`) through `proof.nonvacuous.1`.
  4. Add `Done` to the closure roots in `Report.lean`.
- **Deliverable.** `Done`, `not_done_today`.
- **Accept.** `#print axioms not_done_today` shows no `sorryAx`. W12: the falsifier is
  `not_done_today`; the witness is absent by design until M4.
- **Stop if.** `ValidV3 poseidonRender` is no longer refuted (M4 has landed): then
  `not_done_today` is proved from the `artifact` field or the open headline instead; report which.
- **Guidance.** `native_decide` may occur in `reference`, `artifact`, `vkArtifact` and
  `nonvacuous`: they are tests at a fixture. It may not occur in the cone of `lowering_correct`
  (two separate axiom gates, DG.9). When D-P72's WID.H lands, `Done` gains the F2 fields.

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

### DG.9 — The DONE commit [D-P71: RESTATED]

INFRA · KAT · box 1 h · Sonnet · after DG.3, DG.4, DG.5, DG.6, DG.7, DG.8, PL.H, WID.H, CERT.H

- **Goal.** DONE is asserted by the build and replayed.
- **Needs.** `theorem generator_done : Done poseidonFixtureCalldata`, proved by the other areas;
  `lowering_correct` (PL.H).
- **Does NOT need.** Any new statement.
- **Do.**
  1. Two axiom gates in `ConeReport.lean`:
     `#assert_axioms Midfall.LoweringV3.lowering_correct [propext, Classical.choice, Quot.sound]
     native []` and `#assert_axioms Midfall.Instances.GeneratorDone.generator_done [propext,
     Classical.choice, Quot.sound] native [<every native owner by name>]`.
  2. Add `#replay_native Midfall.Instances.GeneratorDone.generator_done` to `scripts/Report.lean`.
  3. Add the `Done` module and `ConeReport.lean` to `Frozen.sha256`; widen PINNED to every zone.
  4. Delete `not_done_today`. Fill the English statement from the tool output.
- **Deliverable.** The two gates; `STATUS.md` with the final statement.
- **Accept.** `assert_axioms …lowering_correct: ok (3 named, 0 native)`;
  `assert_axioms …generator_done: ok (k named, n native)` with no `unused allowances` line;
  `replay_native …: ok`; `cone_report …lowering_correct: 0 sorried leaves … [CLOSED]`;
  `exhibits: 4 PRESENT, 0 MISSING of 4`; `block_coverage …: 7 INTEGRATED of 7`; CI green.
- **Stop if.** `#replay_native` exceeds the 60 s rule for a single axiom: split that fixture fact;
  do not skip the replay.

---

## Plan-level cards (written with PLAN-V3; decisions as named on each card)

These complete the queue: the cut-over, the W13 repair of the present tree, the four remaining
block rows (each a SKELETON that issues its own PROOF children), the headline and the end-to-end
statement. They follow the same format. Model routing (EXECUTION-V2 W10) is on each card.

### PL.0 — Cut over to PLAN-V3  **[DONE 2026-11-17 — tag `formal/v2-cutover`]**

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

> **D-P71 additions (PL.G, 2026-11-17): clauses the generic rows need, to go into the single text HERE, before ST.6's re-hash.** Each is a typechecked `def PG_*` in `lean/soundness/GeneratorRows.lean` §2 and evaluates `true` at F1; each gets its falsifier in step 5.
> 1. **`gasScan`**: `gas()` occurs only as the gas argument of a call (not "no `gas()`": that would exclude every external-evaluator render, D-P72). Needed by TOT.1.
> 2. **The transcript region** holds the longest absorb run and is disjoint from every walk window (PG-TPBUF). If it follows from `memory.map.WellFormed`, state it as a lemma instead; ROW.TP step 3 checks which.
> 3. **`0x80 ≤ g1IdentityMptr`** (PG-G1ID): `EntryFrameV3'` was declined (D-P64), so zero memory is known from `0x80` only.
> 4. **`2 ≤ numNegLagranges`** (PG-NEGLAG). Step 4 below deletes `WellFormedV3`: keep, in `supported` or in `EnvAgrees`, whichever fact gives `1 ≤ blindingFactors`. If the generator accepts a key with fewer, that is a finding for the human (the lagrange row is false there).
> 5. **One exit scan.** `R.ExitOk` (`SoundnessV3`: the exit shape of the pre-block and the six slices) and `ExitDiscipline (R.prog 0 0)` (`StatementsV3`) are two scans; keep ONE and prove the other from it, or the rows and the headline talk about different facts (PG-EXIT).
> 6. `FR_MODULUS = p` is `constsCoherent` together with `EnvAgrees.modulus`, not `PayloadAgrees` (PG-FRMOD).
> 7. **`returnMptr`** (`Valid.returnMptr`, `Statements.lean:226`, added by Q0.5) is in neither `ValidV3` text: carry it over (the TraceReturn progress row reads it).
>
> **Then card RECON.1b** rebases the D-P71/D-P72/D-P73 evidence onto this single text.


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

### RECON.1b — Rebase the generic evidence onto the single `ValidV3`

GEN · STATEMENT · box 2.5 h · strongest · after RECON.1

- **Goal.** The four evidence files written for D-P71–D-P73 state their theorems over the ONE
  `ValidV3` text RECON.1 produced, and every premise gap is a projection of it.
- **Needs.** RECON.1's text; `lean/statements/GeneratorTheorem.lean` (uses the 18-clause
  `Midfall.LoweringV3.ValidV3`: `hR.noWriters`, `hR.exitDiscipline`);
  `lean/soundness/GeneratorRows.lean` (rows over `R.Valid`; `PG_*` in §2);
  `lean/widening/WideningV3.lean` (`ValidCore` copies the 18-clause text);
  `lean/object/GeneratorCertified.lean` (proves both texts: `generator_certified`,
  `generator_certified_V3`).
- **Do.**
  1. Re-point each file at the single text; delete `ValidCore`'s copy in favour of a projection.
  2. Replace each `PG_*` hypothesis of a child lemma by the projection RECON.1's additions give;
     a `PG_*` with no projection left is reported, not assumed.
  3. Typecheck the M6 exit form `rows_correct (R) (product) (hR : ValidV3 R) : R.ExitOk ∧
     R.SimContracts product ∧ R.ProgContracts product` and `total_correct` together in one file.
  4. `bash docs/plans/V3-evidence/check.sh` green for `statements`, `soundness`, `widening`,
     `object`.
- **Deliverable.** The four files, rebased; the list of `PG_*` that became projections.
- **Accept.** `check.sh` prints `ok` for every file; no file mentions two different `ValidV3`.
- **Stop if.** A gap has no source in the single text: add nothing; report it for RECON.1's owner
  (a clause is missing) or for the human (the class is too wide).

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

### HLP.1 — Helper call summaries [D-P71: RESTATED]

SEM · SKELETON · box 2 h · strongest · after GEN.0, T3.5

- **Goal.** For every render, each helper a row calls has (a) a definition lemma: the block scope
  resolves the name to the body its emitter prints; (b) a word-level summary of that body at an
  arbitrary constant table. A row then executes a call site in one step, for every `R`.
- **Needs.** `GeneratorRows.lean` §3: `HelperIs`, `helperBody`, `fail_is`, `batch_invert_is`,
  `helpers_are`, `helpers_eq` (all PROVED), `BatchInvertPost`, `batch_invert_summary`,
  `bi_forward_loop` (stated). `Midfall/Lowering/GenAst.lean:251-580` (the eight emitters).
  `prooftech/WP.lean:197` (`CSound`). `Blocks/VkLoading.lean:449` (`vk_fail_reverts`: the `fail`
  summary, already for any scope).
- **Does NOT need.** Literal helpers (`helpersLit`), `native_decide`, any Lean-verifier fact, the
  accumulator helpers.
- **VERIFY FIRST.** `check.sh soundness`; `#print axioms helpers_eq` shows the standard three.
- **Do.**
  1. Port §3's definitions and the four proved lemmas (child HLP.1.a).
  2. State one summary per helper in the shape of `batch_invert_summary`: a `StmtsContractAll` over
     `helperBody consts <emitter>` from the callee's entry environment (`params.zip args ++
     bindZeros rets`), post over the returned variables and memory, with the revert arm. Summaries
     with a `staticcall` (`scalar_inv`, `batch_invert`, `ec_pairing`) are stated at
     `permissive (callsOf product)`.
  3. Prove the bridge once: `HelperIs R c g name emit` and a summary of `helperBody R.consts emit`
     give the `CSound` entry for `name` in `R.scope c g` (or, if GEN.0's verdict is P3, the call
     inversion lemma in the shape of `vk_fail_reverts`).
  4. Issue HLP.1.b–d (`batch_invert`) and one card per remaining helper.
- **Deliverable.** The bridge lemma; seven summary statements with witness and falsifier; children in
  `QUEUE.md`.
- **Accept.** `#assert_axioms` on the bridge with `[propext, Classical.choice, Quot.sound] native
  []`; `#cone_sorries` of the bridge is 0; each summary statement has a falsifier (one written word
  changed) shown false by `#eval` of the interpreter at F1.
- **Stop if.** A summary needs a fact about the Lean verifier (wrong level); a helper's body
  inlined inside the helper block differs from its body inlined alone (then `helpers_eq` is false:
  it is PROVED today, so this means the emitter changed).
- **Guidance.** `keccak` stays `keccakOf (readBytes …)`. The existence forms (for TOT.1) are separate
  statements over `StmtsContract` at `callsOf product`; state them in the same card as the all-runs
  form, prove them in TOT.1's children.

### TOT.1 — Totality for every render: `TotalV3 R product` [D-P71: RESTATED]

SEM · PROOF · box 2.5 h · strongest · after ROW.FP, T3.2, GEN.3 (existence form), SIM.6, RECON.1, RECON.3

- **Goal.** `theorem total_correct (R) (product) (hR : R.Valid) (hmp : hasMultiPointSet R = true) :
  Midfall.LoweringV3.TotalV3 R product` with no sorried leaf. The composition is PROVED in the
  evidence; this card and its children close the four leaves.
- **Needs.** `GeneratorRows.lean` §10: `gasFreeScan`, `GasFree`, `gasFree_of_valid`,
  `runBody_gas_oblivious`, `stmts_append_stop`, `LiveTo`, `live_append` (PROVED), `LivePre`,
  `BlockLive`, `block_live`, `prefix_live`, `slices_live`, `total_correct` (PROVED from the leaves).
  `StatementsV3.lean:747-876`. `prooftech/WPX.lean:24` (`wpSS_exists`), `:33` (`Bfun`);
  `prooftech/P1_Exec.lean` (`callsOf_graph`). `SoundnessV3.lean:1182` (`run_join`).
- **Does NOT need.** `LeanAccepts`, `SoundSide`, `CompleteSide`, a snapshot, a fixture, the
  permissive relation.
- **VERIFY FIRST.** `check.sh soundness`; `#cone_sorries total_correct` prints the four leaves and
  `prog_slices_decomp`.
- **Do.**
  1. **What replaces the scan of the literal program.** Add `gasFree : gasFreeScan <fuel>
     (.b (R.prog 0 0)) = true` to `programOk` (RECON.1's text), next to `noWriters`; it is decided
     per circuit like every other clause. `gasFree_of_valid` is then a projection plus address
     independence (`scans_prog_addr_indep`, ST.12). The alternative, a lemma that no emitter prints
     `Op.gas`, is one structural induction per emitter and is not recommended.
  2. TOT.1.a: `runBody_gas_oblivious`.
  3. TOT.1.b–h: `block_live` for each of the seven blocks; TOT.1.i: `prefix_live`.
  4. Falsifier: a toy program that calls an undefined function has no run.
- **Deliverable.** `total_correct`, sorry-free; the `gasFree` clause.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.total_correct [propext, Classical.choice,
  Quot.sound] native []`; `#cone_sorries total_correct` is 0.
- **Stop if.** A block has a path on which the honest relation gives no response (a `staticcall`
  to an address outside the four precompiles): a stuck path in the model; report it. `block_live`
  is asked from a poisoned boundary before `.pcs`: it must not be (`LivePre`); if a block before PCS
  can exit normally with `success = 0`, report the path.
- **Guidance.** Totality does NOT follow from the soundness rows. `LivePre` is clean up to
  `.quotient` because vkLoading, the parser and lagrange end with a reverting guard on `success`
  and the quotient block never assigns it; that fact is part of each early block's liveness card.

### ROW.TP — TranscriptParser row for every render [D-P71: RESTATED]

SEM · SKELETON · box 2.5 h · strongest · after GEN.1, GEN.3, GEN.4, HLP.1, SIM.10, OBJ.4, RECON.3

- **Goal.** `tp_blockSim` and `tp_blockProgS` for every `R`, from named leaves.
- **Needs.** `GeneratorRows.lean` §6: `TEv`, `tpEvents`, `Render.tpEvents`, `tp_events_slots`,
  `inline_g1WalkLoop`, `g1walk_loop_sem`, `XcriptSlots`, `TpPost`, `tp_computes`, `tp_agrees`,
  `tp_poison`, `tp_blockSim` (PROVED from the three leaves), `tp_blockProgS`. Emitter
  `GenAst.lean:1011-1178`; helpers `:320-389`. `SoundnessV3.lean`: `MirrorAt` (:506), `rawSlots`
  (:88), `rawDecode` (:107), `xcript_total` (:1354). Premise gaps PG-CONSTS-TP, PG-FRMOD,
  PG-NOSHADOW, PG-PARSER, PG-TPBUF.
- **Does NOT need.** `ofEip?` or any curve fact outside `Agree`; the algebra of `linearize`; PCS; a
  fixture.
- **VERIFY FIRST.** `check.sh soundness`; `GeneratorRowsWitness.lean` prints `(true, 72, 72)` for the
  schedule and `false` for the mutated plan view.
- **Do.**
  1. State the four helper summaries (child ROW.TP.3) and the three scalar loops (ROW.TP.4:
     instance run, evals spill, q_evals run) in the shape of `g1walk_loop_sem`.
  2. Define the fold of `tpEvents` over a parser state (buffer bytes, three cursors, the walk
     windows, the `success` bit) and state ROW.TP.5: the inlined slice refines that fold, by
     induction over `userPhases` and over `L.lookups`.
  3. State PG-TPBUF as a lemma about the layout (the transcript region holds the longest absorb
     run and is disjoint from every walk window), with its F1 witness. If it is not derivable from
     `memory.map.WellFormed`: PREMISE GAP, stop.
  4. Issue ROW.TP.1–10.
- **Deliverable.** The statements of steps 1–3 with witness and falsifier each; children in
  `QUEUE.md`.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.tp_blockSim [propext, Classical.choice,
  Quot.sound] native []` once the leaves close; `#cone_sorries tp_blockSim` lists exactly
  `tp_computes`, `tp_agrees`, `tp_poison` today.
- **Stop if.** A fact about a decoded point is needed outside `XcriptSlots`' `∀ decoding`; the
  `x3` truncation does not match `Arith.lean:284` for a table other than F1's.
- **Guidance.** The parser is the fold of a list; prove the fold, not the 44 statements. Sonnet-only
  split: step 1 per helper and per loop / step 2 / step 3.

### ROW.Q — Quotient row for every render: route B [D-P71: RESTATED]

> **D-P72 constraint (M9).** As T3.10: the interpreter refinement is proved over a memory window and a dialect parameter. A proof for the verifier's slice only stops WID.17.


SEM · SKELETON · box 2.5 h · strongest · after T3.10, OBJ.2, OBJ.14, OBJ.15, SIM.2, RECON.3

- **Goal.** `q_blockSim` and `q_blockProgS` for every `R` from named leaves, with the builder's
  correctness in scope.
- **Needs.** `GeneratorRows.lean` §7: `qlin_split_loop`, `QInterpRefines`,
  `identityCorrespondence_of_bridge_fixed` (PROVED), `q_blockSim`, `q_blockProgS`. T3.10's contract.
  **Builder sorries now in scope:** `Lowering/Qvm.lean:631` (`qvm_compile_correct_identity`), `:698`
  (`qvm_compile_correct_certifier`), `:713` (`qvm_compile_correct_program`), `:768`
  (`qvm_validated_noBoundsFault`), `:995` (`builder_segments_total`); `Lowering/QvmFold.lean:338`
  (`identityCorrespondence_of_bridge`, refuted by the file at :718-749), `:376`
  (`quotientFold_matches_linearization`), `:434` (`qvm_compile_correct_stream`). Proved and
  reusable: `Qvm.lean:1197` (`evalQuotientIdentityStep_consumed_agrees`), `:1481`
  (`evalQuotientIdentityLoop_fuelNeverBinds`), `:1864` (`…_readsWithinStride`), `:2588`
  (`…_constSlot_namedByWalker`), `:916` (`qvm_validated_windows`), `:334`
  (`evalQuotientExpr_memOfρ`). `SoundnessV3.lean:289` (`linearizeFull`).
- **Does NOT need.** A fixture; route A's reflective check.
- **VERIFY FIRST.** T3.10's contract typechecks. `streamIsInterpretedOnly` (`QvmFold.lean:385`) is
  false at F1 (it has inline and native items): confirm by `#eval`, because the stream theorem at
  :434 assumes it.
- **Do.**
  1. Replace `identityCorrespondence_of_bridge` by the corrected lemma; delete the refuted
     statement in the same commit (W13).
  2. Restate `qvm_compile_correct_stream` without `streamIsInterpretedOnly`: the fold walk over ALL
     item kinds (inline, native permutation, native lookup, native identity, structured tail), each
     with its own value lemma. Witness at F1; falsifier: one gap of `selectorFold` off by one
     (`foldGapOffByOneFlipsBucket_ok`, `QvmFold.lean:495`).
  3. State the SEM leaves: ROW.Q.1 (linearization loop), ROW.Q.3 (interpreter, per arm family),
     ROW.Q.5 (one per generated-line family, as a list induction over its block producer's twin).
  4. State the ALG leaf: the folded word and the selector accumulators are `linearizeFull`'s
     `linCom` evaluation and buckets, under `SoundSide`.
  5. Issue the children below.
- **Deliverable.** The corrected bridge in the tree; the restated stream theorem; the leaf
  statements with witness and falsifier each; children in `QUEUE.md`.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.identityCorrespondence_of_bridge_fixed
  [propext, Classical.choice, Quot.sound] native []`; `#cone_sorries q_blockSim` lists the named
  leaves only; `grep -c 'identityCorrespondence_of_bridge ' Midfall/` shows the refuted statement
  gone.
- **Stop if.** The six line families have no AST twin of their block producer (PG-Q-OBJECT): the
  families cannot be inducted over; write the EMIT cards for the twins and stop. The logup identity
  the contract computes differs from `linearize`'s outside the `SoundSide` set: report both.
- **Guidance.** Children and sizes (boxes, not time): ROW.Q.1 linearization loop (1); ROW.Q.2 AST
  twins of the six block producers (6 EMIT, Sonnet once OBJ.15's pattern exists); ROW.Q.3
  interpreter arms (one per family from T3.10's table, about 6, plus the dispatch loop, 1); ROW.Q.4
  frame valuation `Agrees` and the program/constant window lemmas from `Inv .vk` (2); ROW.Q.5
  families (6); ROW.Q.6 `qvm_compile_correct_identity` by the emitter's fuel-bounded mutual block:
  one card per peephole (pow5, modarith7, limb family, run decomposition) and one for the plain
  cases (5); ROW.Q.7 certifier, program, `builder_segments_total` (3); ROW.Q.8
  `qvm_validated_noBoundsFault` from the three proved per-arm facts (1); ROW.Q.9 fold:
  `quotientFold_matches_linearization` (`horner_reverse`, bucket gaps, `groupedAdd`) (3); ROW.Q.10
  glue (1). Total about 30.

### ROW.PCS — PCS row for every render [D-P71: RESTATED]

SEM · SKELETON · box 2.5 h · strongest · after ROW.Q, SIM.12, T3.9, GEN.4, the M1 exit gate, RECON.3

- **Goal.** `pcs_blockSim` and `pcs_blockProgS` for every `R` from named leaves.
- **Needs.** `GeneratorRows.lean` §8: `PG_pcsEmits`, `pcs_slice_of_ok`, `pcs_slice_of_fault` (both
  PROVED), `wPowers`, `pcs_b2_sem`, `decode_exists`, `pcs_blockSim`, `pcs_blockProgS`. Emitters
  `GenAstPcs.lean:131` (block 1), `:163` (2), `:193` (3), `:254`, `:317` (4), `:342-473` (5), `:485`
  (6), `:587` (`computationsAst`); `GenAstDispatch.lean:131`. `SoundnessV3.lean:197`
  (`decodeCalldata_isSome_iff`), `:577` (`hasMultiPointSet`). `scalar_inv` (`Lowering/GenAst.lean:441`).
- **Does NOT need.** The pairing; `DualMSM.check`; a fixture.
- **VERIFY FIRST.** `GeneratorRowsWitness.lean` prints `225` and `"ok, 8 blocks"` for F1's plan view.
- **Do.**
  1. PG-PCS-EMIT: prove `PG_pcsEmits R` from `hR` and `SimPins.multiPoint`, or name the fault arm
     that `Valid` does not exclude (`GenAstPcs.lean:433`, `:407`, `:461`) and stop.
  2. Per block, state the SEM leaf over `Stmt.block (inline consts (pcsBlockNAst …))` in the shape
     of `pcs_b2_sem`: block 1 by induction over the two rotation ranges; block 3 by induction over
     the sets (rolled arm: one loop, bound = commitments in the set); block 4 by induction over the
     reversed sets with the `scalar_inv` summary; block 5 with the pair-counter invariant; block 6
     fixed text.
  3. State the coverage invariant as a fact about `computationsAst`'s staging list: every G1
     window of `MirrorAt` is the source of some staged pair. No Yul in the statement.
  4. `decode_exists` (stated) closes the new obligation from step 3 and `Holds.g1Decodes`.
  5. `x = 0`: with `hasMultiPointSet` some set block computes `scalar_inv` of a product containing
     `pt_j − pt_k = 0`, which reverts.
  6. ALG leaf: under a decoding the two results are `toEip` of the Lean `multiPrepare`'s.
- **Deliverable.** The statements of steps 2, 3, 5, 6 with witness and falsifier each; children.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.pcs_slice_of_ok [propext, Classical.choice,
  Quot.sound] native []`; `#cone_sorries pcs_blockSim` lists the named leaves only; falsifier for
  step 5 on a toy plan whose sets are all singletons.
- **Stop if.** A G1 window that no MSM reads: a soundness defect of the generated contract; report
  to the human at once. Step 1 fails: do not add the premise.
- **Guidance.** Children: ROW.PCS.1 emit lemma, .2 block 2, .3 block 1, .4 block 3 straight arm, .5
  block 3 rolled loop, .6 `scalar_inv` summary, .7 block 4, .8 block 5 staging, .9 `decode_exists`,
  .10 coverage, .11 block 5 call and block 6, .12 `x = 0`, .13 ALG, .14 glue and poison. Blocks 3–5
  bind variables whose NAMES depend on an index (`q_eval_set_k`, `x4_pow_s`): the environment
  invariant must be stated over `toString`.

### ROW.FP — FinalPairing row for every render [D-P71: RESTATED]

SEM · PROOF · box 2.5 h · strongest · after ROW.PCS, PL.1, REF.5, HLP.1, RECON.1, RECON.3

- **Goal.** `fp_blockSim` and `fp_blockProgS` for every `R`, proved.
- **Needs.** `GeneratorRows.lean` §9: `fp_poison` (PROVED from the tree's `fp_stmt_steps`),
  `ec_pairing_sem`, `fp_blockSim`, `fp_blockProgS`, `PG_g2Slots`. `Blocks/FinalPairing.lean`:
  `fp_pairing_algebra` (:278, true as stated), `ec_pairing_contract` (:314, false as stated:
  RV-23), `fp_stmt_steps` (:352), `fpFrame` (:148). `SoundnessV3.lean:1314`
  (`fp_blockSim_of_blockSound`). Emitters `GenAst.lean:649-654`, `:265-292`.
- **Does NOT need.** A pairing implementation; a fixture; loops.
- **VERIFY FIRST.** `check.sh soundness`; `ValidV3` supplies `PayloadAgrees.g2Base`, `.negSG2`
  (PG-G2SLOTS); if not, STOP.
- **Do.**
  1. Close `ec_pairing_sem` by GEN.0's parametric execution with the `fail` summary: the
     `staticcall` forks over every permitted response; on success the response is the honest one.
  2. Land the counterexample to the old `ec_pairing_contract` (`success = 3`) and delete the old
     statement (W13).
  3. `fp_stmt_steps`: the first statement reverts on `success = 0` (`vk_guard_fires`).
  4. From a staged boundary at `.pcs`: the frame in memory is `fpFrame R S` (`Inv .pcs`'s two
     `holdsG1`, PG-G2SLOTS); `fp_pairing_algebra` turns the product's answer into `DualMSM.check`;
     `Inv.pairing` from `Inv .pcs` clause by clause; `agree_of_one`.
  5. Progress: under `LeanAccepts` the honest call answers `true`.
- **Deliverable.** `fp_blockSim`, `fp_blockProgS`, `ec_pairing_sem`, sorry-free; the old contract
  deleted.
- **Accept.** `#assert_axioms` on the three with `[propext, Classical.choice, Quot.sound] native
  []`; `#cone_sorries fp_blockSim` is 0.
- **Stop if.** A base-point pin is not derivable from `PayloadAgrees` (D-P62 or REF.7 incomplete).
  `ec_pairing_sem`'s frame order (RHS first) does not match `fpFrame`: report both lists.
- **Guidance.** The helper's `leave` on `success = 0` is never reached: the slice's guard reverts
  first. Sonnet-only split: step 1 / 2 / 3 / 4 frame / 4 algebra and `Inv` / 5.

### PL.H — The headline: `lowering_correct` [D-P71: RESTATED]

INFRA · PROOF · box 1 h · strongest · after every ROW card and its children, TOT.1, SIM.5, SIM.6, ST.11–ST.13, RECON.2

- **Goal.** `theorem lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
  (hR : ValidV3 R) : LoweringEquivalenceV3 R product`, sorry-free, with no fixture and no
  `native_decide` in its cone.
- **Needs.** `docs/plans/V3-evidence/lean/statements/GeneratorTheorem.lean` (§1–§2: the four
  obligations `twoOutcomes_correct`, `rejects_correct`, `complete_correct`, `total_correct`, and
  the proved composition through `lowering_equivalenceV3_of`);
  `lean/soundness/GeneratorRows.lean` (`rows_correct`, `lowering_correct_of_rows`,
  `rejectsV3_of_rows`, `total_correct`); RECON.2's composition; every ROW card's theorem.
- **Does NOT need.** Any new proof, any fixture, `poseidonRender`. If a proof is needed, a leaf
  was mis-stated: stop.
- **VERIFY FIRST.** `bash docs/plans/V3-evidence/check.sh statements` and `soundness` pass;
  `#cone_report` on `rows_correct` prints `0 sorried leaves`.
- **Do.**
  1. Port `GeneratorTheorem.lean` §1–§2 verbatim into the module RECON.2 names for the headline.
  2. Replace the three `sorry`s: `rejects_correct` by `rejectsV3_of_rows` applied to `rows_correct`;
     `complete_correct` by the progress composition; `total_correct` by TOT.1's theorem.
  3. Add `#assert_axioms Midfall.LoweringV3.lowering_correct [propext, Classical.choice,
     Quot.sound] native []` to the build.
  4. Delete the fixture headline `lowering_equivalence_poseidon` if PL.1 has not already; keep
     ONE `example` instantiating `lowering_correct` at `poseidonRender` as a test.
- **Deliverable.** `lowering_correct`; the axiom gate.
- **Accept.** The `#assert_axioms` line prints `ok (3 named, 0 native)`;
  `#cone_report lowering_correct` prints `0 sorried leaves`; the falsifier
  `lowering_correct_needs_valid` (`GeneratorTheorem.lean` §4) is in the tree and has the standard
  three axioms.
- **Stop if.** `#assert_axioms` reports a `native_decide` axiom: a fixture fact entered the cone.
  Report the owner declaration and the row it came through; do not extend the list.
- **Guidance.** `SimPins R` is NOT a consequence of validity (`simPins_not_of_valid`,
  `GeneratorRows.lean`): it comes from the headline's codec hypothesis (`simPins_of_laws`).
  This card proves `lowering_correct` for the BASE class only (no accumulator, embedded
  evaluator): the rows are in the widened shape after RECON.3, and the base-class headline is
  read off through RECON.3's reduction. `lowering_correctW` for the whole widened class is WID.H,
  which comes after this card and after the WID rows.

### PL.E — End to end and the English statement [D-P71: RESTATED]

ALG · PROOF · box 2.5 h · strongest · after PL.H

- **Goal.** `theorem end_to_end (R) (product) (hR : ValidV3 R) … : EndToEndV3 R product hR
  (lowering_correct R product hR) …` for every render, and the English statement of PLAN-V3 §6 in
  `STATUS.md`.
- **Needs.** `EndToEndV3` (`StatementsV3.lean:946`); `Lowering.verifyNative_iff_msgs_codec`
  (proved); `entryFrame_inhabitedV3`; `calldata_roundtrip`, `calldata_canonical`,
  `repack_spec_of_decodeRust` (`Lowering/Calldata.lean:731, :790, :1276`, open) **for every
  layout a valid render has**; `cdSize_of_decodes` (proved); `G1CodecLawsV3`.
- **Does NOT need.** Any Yul; any fixture.
- **Do.**
  1. Copy `verifyNative_iff_msgs_codec` into a V2 module (measure its cone with `#cone_in`).
  2. Prove the three calldata lemmas for a layout `L` with
     `ProofCalldataLayout.fromProtocol … = .ok L` (the `ValidV3.layout` clause). Each is one
     2.5 h child if it does not close in this box: issue it with the exact goal.
  3. Derive `end_to_end`; add `#assert_axioms` with an empty native list.
  4. Write the English statement from the report's output, itemised as §6 lists.
- **Deliverable.** `theorem end_to_end`; the STATUS section.
- **Accept.** `#assert_axioms end_to_end [propext, Classical.choice, Quot.sound] native []`;
  one `example` at `poseidonRender` as a test; every item of §6's English statement is present
  and names the tool output it came from.
- **Stop if.** A calldata lemma is false for some valid layout: land the counterexample layout
  (NEGATIVE) and ask the human; do not restrict the class.

## Area GEN — the generator theorem  **[D-P71, signed 2026-11-17]**

Drafted 2026-11-17 at `c22b51a` with `docs/DECISIONS-PENDING.md` §13; D-P71 was signed the same day
(`design.md`). PL.G has run (2026-11-17): the cards D-P71 lists are restated. GEN.1 replaces T3.6.
Ids: `GEN.n`; `PL.G` is plan-level. GEN.4 and the row children are in area GEN-ROWS below.

**Context for GEN.0–GEN.4.** Under D-P71 a block row is proved for every render `R` from validity,
not at `poseidonRender`. Three things that are numerals on a literal slice are then variables: the
constants the inliner substitutes (`R.consts`), the function scope (the hoisted helpers of `R`),
and loop bounds. The design pass of 2026-11-17 measured the first two on the vkLoading block and
proved a rule for the third; both are evidence files (`bash docs/plans/V3-evidence/check.sh
prooftech`: `VKP` and `LoopRule` print `ok`), with the memo `design/prooftech-generic.md`:

| variant, on the parametric vkLoading body | leaves | `wp_run` | kernel | first stuck term |
|---|---|---|---|---|
| literal `vk_all` (the fixture slice) | 4 | 106 ms | 365 ms | — |
| P1: `wp_run` on `vkBody consts …` as it is | 1, stuck | < 50 ms | 16 ms | `Expr.rec … (vkSite "EXPECTED_VK_CODEHASH_WORD" consts)` |
| **P2: rewrite with `vkBody_eq_vkBodyV`, then `wp_run`** | **7, all closed** | 86–100 ms | 225–243 ms | — |
| P2 with the `VK_MPTR` hypothesis removed (falsifier) | 3, stuck | < 50 ms | — | `Expr.rec … (vkSite "VK_MPTR" consts)` |

**Verdict: P2.** The seven leaves are the literal run's four plus one scope obligation per `fail`
call site. The script every row copies: (1) bring the emitted group to its normal form with
constant sites as free `Nat` variables (one `consts.lookup "X" = some x` hypothesis per name);
(2) summarise each helper (`CSound`); (3) `wp_run`; (4) close the residue with the word layer.

> **GEN.2** was rewritten by PL.G and moved to area WID (it needs the decider exporter, WID.3).

### GEN.0 — Land parametric execution: `vk_all_param` for every constant table and scope

SEM · PORT · box 2 h · Sonnet · after T3.1b

- **Goal.** `vkBodyV`, `vkBody_eq_vkBodyV`, `vk_all_param`, `vk_all_param_mem`, `Cfail_sound` and
  `Cfail_live` are in the tree, and the P1/P2 table above is re-measured at the tip.
- **Needs.** `docs/plans/V3-evidence/lean/prooftech/VKP.lean` (426 lines; one named sorry,
  `wpSS_exists_C`, which is GEN.1's); T3.1's landed engine (`wp_sound`, `CSound`) and T3.1b's (`wp_run`, `WPX`);
  `Midfall/LoweringV2/Blocks/VkLoading.lean` (`vkSite` :94, `vkBody` :152);
  `Blocks/TraceReturn.lean` (`tr_fail_body`: the fact the `fail` summary is built from).
- **Does NOT need.** `Inv`, `Clean`, `StageInv`, `Frame`, the Lean verifier, any algebra, any
  other block, any fixture, `native_decide`.
- **VERIFY FIRST.** `bash docs/plans/V3-evidence/check.sh prooftech`: `VKP` prints `ok` with 1
  sorry warning.
- **Do.**
  1. Port `VKP.lean` verbatim into the module T3.1 created for the engine's clients; change only
     imports and the namespace.
  2. Re-measure: with `set_option profiler true` and `profiler.threshold 50`, record `wp_run` and
     kernel milliseconds for `vk_all_param`; delete the `hMVk` rewrite and record that `wp_run`
     stops at `vkSite "VK_MPTR" consts` (the falsifier); restore.
  3. `#assert_axioms` on `vk_all_param`, `vk_all_param_mem`, `Cfail_sound`, `Cfail_live`.
  4. Register `wpSS_exists_C` in the sorry register (owner: T3.2).
  5. `VKP.lean` sets `maxRecDepth 10000` at `:221` and `:279`, as the literal `VK.lean` does. The
     rules forbid raising it. Remove the option and re-check: if `vk_all_param` still closes,
     land it without; if not, land it WITH the option, record the smallest depth that works, and
     put the question under "Waiting on human" (an exception to the rule is not pre-approved).
- **Deliverable.** The six declarations; the re-measured table in the report.
- **Accept.** Point P of PLAN-V3 §5 M5: `vk_all_param` closes with 7 leaves, kernel ≤ 2 s,
  elaboration ≤ 10 s, no `maxHeartbeats` raise; `maxRecDepth` as step 5 reports.
  `#assert_axioms … [propext, Classical.choice, Quot.sound] native []` passes on all four.
- **Stop if.** The port does not reach 7 closed leaves at the tip: the verdict is no longer P2.
  Land the stuck goal verbatim and stop. Under D-P71 this goes to the human.
- **Guidance.** The constants are `Nat` (`Inline.Consts = List (String × Nat)`,
  `Lowering/InlineConstants.lean:256`), 15 bound names and 2 unbound (`vk`, `success`) at 20
  sites. The scope hypothesis is `lookupFun funs "fail" = some (failFDecl, funs')`. Never `simp`
  the `wp` term. The literal run needed `set_option wpLets false`. **Do not wrap `lake env lean`
  in `perl -e 'alarm …'`: on timeout it kills `lake` and orphans `lean`.** Export
  `LEAN_PATH="$(lake env printenv LEAN_PATH)"` and put the alarm on `lean` itself.

### GEN.3 — Land the loop rule for a symbolic bound

SEM · PORT · box 1.5 h · Sonnet · after T3.1b

- **Goal.** One invariant rule for a Yul `for` loop whose bound is a variable, usable inside a
  `wp`/`AllRuns` goal, in the tree with its witness and its falsifiers.
- **Needs.** `docs/plans/V3-evidence/lean/prooftech/LoopRule.lean` (522 lines, no sorry):
  `wpIter`, `allRuns_loop`, `allRuns_for_cons_wp`, `allRuns_for_cons_wp_count`, the witness
  `sumLoop_all`, the falsifiers `loopRuleNoPres_false` and `sumLoop_all_needs_bound`, and the
  table of the verifier's loops in its §5.
- **Does NOT need.** Any block, any fixture, `Midfall/Yul/Contracts.lean:298`
  (`countdown_or_halt` needs a count and `Inv 0 → guard = 0`; this rule needs neither).
- **VERIFY FIRST.** `check.sh prooftech`: `LoopRule` prints `ok` with 0 sorry warnings.
- **Do.** Port the file verbatim next to the engine; `#assert_axioms` on the three rules and the
  witness; copy the loop table into the module docstring.
- **Deliverable.**

  ```lean
  theorem allRuns_for_cons_wp (hB : BSound D B) (hC : CSound D C) {n} {funs} {V} {st}
      {init : Block D.Op} {c : Expr D.Op} {post body rest : Block D.Op}
      (Inv : VEnv D → D.State → Prop) {Q : VEnv D → D.State → Outcome → Prop}
      (hinit : wpSS D B C n (hoist D init :: funs) V st init fun Vi sti oi =>
          match oi with | .normal => Inv Vi sti | .halt => Q (restore V Vi) sti .halt | _ => False)
      (hstep : ∀ Vi sti, Inv Vi sti →
          wpIter D B C n (hoist D init :: funs) Vi sti c post body Inv fun Vend stend o =>
            match o with
            | .normal => Hold (AllRuns funs (restore V Vend) stend rest Q)
            | _ => Q (restore V Vend) stend o) :
      AllRuns funs V st (.forLoop init c post body :: rest) Q
  ```

- **Accept.** `#assert_axioms` on `allRuns_loop`, `allRuns_for_cons_wp`,
  `allRuns_for_cons_wp_count`, `sumLoop_all`: `[propext, Classical.choice, Quot.sound] native []`
  (measured: `[propext]` only). Both falsifiers are in the tree. This is half of point L of
  PLAN-V3 §5 M5; T3.9.a is the other half.
- **Stop if.** A statement stops elaborating against the landed engine: report the first error;
  do not restate the rule.
- **Guidance.** `wpIter` is `wpL` for one iteration with the recursive call replaced by `Inv`, so
  the rule needs no variant: termination is not its business (totality is TOT.1's).
  `sumLoop_all_needs_bound` shows what a dropped no-overflow hypothesis costs: the witness fails
  at `n = 2^256`. Every loop card states its bound hypothesis and its falsifier in that form.

### T3.1b — Land the `wp_run` tactic and the existence statements

SEM · PORT · box 1.5 h · Sonnet · after T3.1

- **Goal.** `wp_run` and the statements of `WPX.lean` are in the tree, so that GEN.0 and GEN.3
  (which import both) compile. T3.4 used to land the tactic and is dropped.
- **Needs.** `docs/plans/V3-evidence/lean/prooftech/WPTac.lean` (`wp_run` :221, the options
  `wpLets`, `wpDebug`), `WPX.lean` (`BLive`, `wpSS_exists` :24; 3 sorry warnings); T3.1's module.
- **Does NOT need.** Any block, any fixture, `Lits.lean`, `TR.lean`, `VK.lean`.
- **VERIFY FIRST.** `bash docs/plans/V3-evidence/check.sh prooftech`: `WPTac` and `WPX` print `ok`.
- **Do.** Port the two files verbatim next to the engine; register `WPX.lean`'s three sorries
  (owner: T3.2); `#print axioms` on one closed `wp_run` example (the engine's own test).
- **Deliverable.** The tactic and the statements in the tree.
- **Accept.** `lake build` green; the example closes; `Frozen.sha256` unchanged.
- **Stop if.** `WPTac.lean` depends on `Lits.lean` or another fixture file: report the import; do
  not land a fixture file to satisfy it.

### GEN.1 — The vkLoading row for every render (calibration B; replaces T3.6)

SEM · PROOF · box 2.5 h · strongest · after GEN.0, SIM.8, T3.2, T3.5, T3.11, OBJ.4, RECON.3

- **Goal.** Close the three sorries SIM.8 leaves behind `vk_blockSim` for every `R` with
  `hR : R.Valid` (the name in the tree; `ValidV3 R` after RECON.1), and measure lines per token
  and hours. This is the first block row proved on the D-P71 route and the number every later
  estimate starts from.
- **Needs.** SIM.8's statements (`vk_sim_clean`, `vk_poison_walk`, `vk_prog`; today only
  `vk_poison_walk` exists, `Blocks/VkLoading.lean:735`, with sorries at `:728`, `:743`, `:756`);
  GEN.0's `vk_all_param`, `vk_all_param_mem`, `Cfail_sound`, `Cfail_live`, and the statement
  `wpSS_exists_C` with `CLive`; `Blocks/VkLoading.lean` §1–§5 (`vk_slice` :189,
  `vk_poison_step` :631, `vk_get_set_of_some` :611, `vkPins_of_valid` :685,
  `vkProgressPins_of_valid` :688); T3.5's simp set `yul_word`; `StageInv` at `.start` and `.vk`.
- **Does NOT need.** Loops, `staticcall`, `ZMod`, any fixture, `native_decide`. (True for the base
  class only: the accumulator arm, with two literal-bound loops and two `staticcall`s, is WID.13.)
- **VERIFY FIRST.** GEN.0 is merged with verdict P2. T3.11's exhibit is PRESENT (W14).
  `grep -c sorry Midfall/LoweringV2/Blocks/VkLoading.lean` counts exactly the three named above.
  **The 15 constant lookups:** `vkPins` and `vkProgressPins` give 4 of them; the other 11 come
  from the constant-coherence clause (OBJ.4 / `programOk`'s `constsCoherent`). If that clause is
  not in the tree, this card is NOT READY.
- **Do.**
  1. Instantiate `vk_all_param_mem`'s 17 hypotheses: 4 from `hR.vkPins` / `hR.vkProgressPins`,
     11 from the coherence clause, 2 (`vk`, `success` unbound) from `noShadow`; the scope
     hypothesis from `fail_is` (`GeneratorRows.lean`, proved for every `R`).
  2. `vk_sim_clean`: derive `StageInv .vk` from the residue and the memory fact
     (`st'.memory = copyInto st.memory mVk 1 payLen (extCodeOf vk)`). Assemble the `.vk` clauses
     one at a time with `if_pos` / `if_neg` on the `Checkpoint.idx` guards; do not normalise the
     whole chain (`VkLoading.lean:710-712`: that exceeds the default heartbeats). The bounds the
     memory step needs (`mVk, payLen < 2^256`, `vkLen = payLen + 1`, `cI + 32·n < 2^256`) come
     from the layout clause and `cdBound`: list each with its source; a bound with no source is
     a PREMISE GAP.
  3. `vk_poison_walk`: from a poisoned boundary every run reverts; `vk_poison_step` is the
     content of the six header guards.
  4. `vk_prog` (the existence half). **`wpSS_exists` does not apply**: it assumes no call
     summaries, and without the `fail` summary `wp_run` leaves three leaves stuck at
     `lookupFun … "fail"` (measured). Use `wpSS_exists_C` (the liveness form; T3.2 proves it;
     `Cfail_live` is in `VKP.lean`) to exhibit the run. Run this half at the honest dialect
     (`Bfun`), not at `Bopen`.
  5. Test, not proof: one `example` instantiating the row at `poseidonRender`, and SIM.8's
     falsifier re-checked.
  6. Report: new lines, lines per token (the slice is 225 tokens), elaboration and kernel
     seconds, hours.
- **Deliverable.** `vk_blockSim` and the progress row, sorry-free, for every `R`.
- **Accept.** Point B: `#assert_axioms` on both rows with `[propext, Classical.choice,
  Quot.sound] native []`; at most 300 new lines; elaboration
  ≤ 30 s and kernel ≤ 5 s for the file; no heartbeat raise; the `example` typechecks.
- **Stop if.** A clause of `StageInv .vk` needs a fact that neither the block nor validity
  supplies: PREMISE GAP with the exact goal; do not add a pin. At 1 h with less than a third
  done: stop (EXECUTION-V2). **A missed Accept line is reported to the human (D-P71); the
  per-fixture row is not a fallback.**
- **Guidance.** The block is one `Stmt.block` of thirteen statements; a normal exit has
  `success = 1`, so the clean walk does not use the `normal ∧ Poisoned` arm
  (`VkLoading.lean:19-26`). The block's exit environment is `restore V Vb`; reading `success`
  back through it needs `vk_get_set_of_some`. Sonnet-only split: step 1 / step 2 / step 3 / step 4.

### PL.G — Restate the plan for the generator theorem (D-P71)  **[DONE 2026-11-17, in the plan session]**

INFRA · DECISION · box 2.5 h · the plan session with the human, no subagent · after —

- **Goal.** Every file the orchestrator reads states D-P71: the goal is `lowering_correct`, rows
  are proved for every render, fixtures are tests.
- **Needs.** `design.md` D-P71; `docs/DECISIONS-PENDING.md` §13 (the amendment and card tables);
  PLAN-V3 §0, §2.2, §5 M5–M8, §6, §10.3; `v2-bundle/docs/GOAL-PROMPT.md`; the V3 table of
  `QUEUE.md`; `V3-evidence/lean/statements/StatementsV3.lean`, `soundness/SoundnessV3.lean`.
- **Does NOT need.** GEN.0's verdict: the technology paragraph of M5 points at GEN.0's report
  and is completed when it lands. No Lean proof.
- **Do.**
  1. PLAN-V3 §0: the objective is the generator theorem for the class `SupportedV3`; F1 is the
     test circuit. §2.2: add row 71. §1/§2: one line each on D-P24, D-P44 clause 4, D-P68, D-P69.
  2. §5 M5: the cards become T3.0, T3.1, T3.2, T3.5, T3.7, T3.8, HLP.1, GEN.0, GEN.1, T3.9
     restated, T3.10 with route B only. Replace "Why per deployment" and the A–C threshold rows
     by GEN.0's and GEN.1's Accept lines. Exit gate: the rows for `.traceReturn`, `.vkLoading`,
     `.lagrange` and the prefix proved for every `R`.
  3. §5 M6: every row statement takes `(R) (hR : R.ValidV3)`. Exit gate:
     `theorem rows_correct (R) (product) (hR : R.ValidV3) : R.SimContracts product ∧
     R.ProgContracts product ∧ TotalV3 R product` with `0 sorried leaves`.
  4. §5 M7, M8: PL.H proves `lowering_correct`. PL.E proves the end-to-end theorem for every
     `R`; the three calldata lemmas (`Lowering/Calldata.lean:731, :790, :1276`) are then needed
     for every layout, not at the fixture layout.
  5. §6: `Done` becomes
     `headline : ∀ R product, R.ValidV3 → LoweringEquivalenceV3 R product` (stated under the
     section variables), `nonvacuous : poseidonRender.ValidV3 ∧ ∃ product, GateAtV3 poseidonRender
     product fixtureCd`, and `reference`, `artifact`, `vkArtifact` unchanged. Two axiom gates:
     `#assert_axioms lowering_correct [propext, Classical.choice, Quot.sound]` with an empty
     native list, and the frozen owner list for `Done`. Rewrite the English statement: the claim
     is for every circuit in the class; the per-circuit obligation is the `ValidV3` check.
  6. `PLAN-V3-cards.md`: restate T3.9, T3.10, SIM.6, TOT.1, ROW.TP, ROW.Q, ROW.PCS, ROW.FP, PL.H,
     PL.E, DG.4 in place, each heading tagged `[D-P71: RESTATED]`; tag T3.4 `[D-P71: DROPPED]`,
     T3.6 `[D-P71: REPLACED BY GEN.1]`, T3.3 and T3.11 `[D-P71: TEST ONLY]`. Add one card for the
     loop rule with a symbolic bound that T3.9 restated needs
     (`Midfall/Yul/Contracts.lean:298`, `ExecLoopAll.countdown_or_halt`, is the starting point).
  7. `QUEUE.md`: set the `after` columns that named T3.4 or T3.6 to GEN.1 and clear the
     "D-P71: wait for PL.G" notes. `GOAL-PROMPT.md`: the GOAL, DONE and Fixtures paragraphs.
     `STATUS.md`: one line.
- **Deliverable.** The edits above in one commit.
- **Accept.** `grep -n "poseidon_done\|lowering_equivalence_poseidon\|end_to_end_poseidon\|at the
  deployment\|per deployment"` over PLAN-V3 §0–§10, the cards and the goal prompt returns only
  lines that are history or tests and say so. Every restated statement typechecks in a
  `V3-evidence` file, with its witness (the instance at `poseidonRender`) and its falsifier (W12).
- **Stop if.** A restated row is false for some `R` with `R.ValidV3` (the class is too wide or a
  pin is missing): do not add a hypothesis; write the counterexample and ask the human.
- **Guidance.** The statements are already generic: `BlockSim` (`SoundnessV3.lean:559`),
  `BlockProgS` (:1065) and `lowering_equivalence_of_stages` (:1226) take any `R`. The rewrite is
  of who discharges the row hypotheses, not of the architecture.

## Area GEN-ROWS — children of the restated rows  **[D-P71]**

The nine row cards above (`T3.9`, `T3.10`, `SIM.6`, `HLP.1`, `TOT.1`, `ROW.TP`, `ROW.Q`, `ROW.PCS`,
`ROW.FP`) were restated in place by PL.G for every render; their headings carry `[D-P71: RESTATED]`.
The cards below are their PROOF and STATEMENT children. Evidence, typechecked by
`bash docs/plans/V3-evidence/check.sh soundness`: `lean/soundness/GeneratorRows.lean` (40 named
open obligations; the composition, `rows_correct`'s reduction and the helper-scope lemmas are
proved) and `GeneratorRowsWitness.lean` (tests at F1; `native_decide` occurs only there). Memo:
`design/rows-generic.md`.

- **Every signature quoted in a card is a declaration of `GeneratorRows.lean`; find it by name.**
- `R.Valid` is today's name. After RECON.1 read `ValidV3 R`; each `PG_*` definition marked [V3]
  in `GeneratorRows.lean` §2 becomes a projection of `hR`. After RECON.3 (D-P72) the row families
  are the `W` families and each row is transported by the proved reduction.
- **Routing rule.** `Sonnet` only where the statement is typechecked AND the proof pattern has
  been run once in the tree. Otherwise `strongest`, with the Sonnet-only split in the card's
  Guidance (PLAN-V3 §7: children of at most one hour, each with the parent's evidence file and
  stop conditions).
- **A card's first job is to try to falsify its statement** (W12): the loop and summary
  statements are typechecked and have a witness of their hypotheses at F1, nothing more.
- **Where the children land.** Card GEN.5 lands the statements; each child closes its lemma in
  the file of its block (GEN.5's Guidance). A child that mentions `StageInv`, `BlockSim` or
  `Poisoned` is briefed in the shape RECON.3 landed. No child is READY before GEN.5.
- A `PREMISE GAP` (`PG_*`) is never added as a hypothesis by a subagent. PL.G's table in PLAN-V3
  §5 M6 says which card or which `ValidV3` clause supplies each.

### GEN.5 — Land the generic row statements and their shared definitions

SEM · PORT · box 2 h · Sonnet · after RECON.3, RECON.1b

- **Goal.** `GeneratorRows.lean` is in the tree as `Midfall/LoweringV2/RowsGen.lean`: §0 (shared
  definitions: `seg`, `wMulmod`, `wPow2`, `lagInner`, the tactic `kernel_rfl`), §1 (the
  composition), the row statements and their stated children as named sorries, registered by
  owner card.
- **Needs.** `docs/plans/V3-evidence/lean/soundness/GeneratorRows.lean` as rebased by RECON.1b and
  re-pointed by RECON.3; `GeneratorRowsWitness.lean` (lands under `Midfall/Instances/`).
- **Do.** Port verbatim; change imports and the namespace; register each sorry with the card id
  that closes it (the card whose Goal names the lemma).
- **Deliverable.** The module; the register rows; the witness module.
- **Accept.** `lake build` green; `#print axioms` on `sim_rows`, `prog_rows`, `helpers_eq`,
  `fail_is`, `batch_invert_is`: no `sorryAx`; the witness module's tests print as in the
  evidence log.
- **Stop if.** A statement no longer elaborates after RECON.3's re-pointing: report the first
  error; do not restate.
- **Guidance.** After this card every GEN-ROWS child closes a lemma of `RowsGen.lean` in a file
  of its block: `Midfall/LoweringV2/Blocks/{Prefix,Helpers,Lagrange,Transcript,Quotient,Pcs,
  FinalPairing}Gen.lean`. Names in the children's Accept lines are the evidence names (namespace
  `Midfall.LoweringV2.V3.Gen`); use the landed namespace in `#assert_axioms`.

### GEN.4 — The inliner distributes over a concatenation

GEN · PROOF · box 2 h · strongest · after —

- **Goal.** Isolate one statement group of an emitter whose output contains a symbolic list, so that
  the list-induction children of ROW.TP and ROW.PCS can be stated about a group.
- **Needs.** `Midfall/Lowering/InlineConstants.lean:320-389` (`inlineStmtStep`, `inlineStep`,
  `inlineScan`, `boundOf` :263); `Midfall/LoweringV2/ProgramLemmas.lean:27` (`inline_append`, a
  sorry); evidence `GeneratorRows.lean`: `inlineScan_append`.
- **Does NOT need.** Any semantics, any render, `noShadow`.
- **VERIFY FIRST.** `bash docs/plans/V3-evidence/check.sh soundness` passes; `inlineScan_append` is
  still a sorry there.
- **Do.**
  1. Prove the accumulator lemma: for the fold of `inlineStep`, `(foldl f acc (a ++ b)) = foldl f
     (foldl f acc a) b` (`List.foldl_append`), and by induction on `a` that the fold's `sh` field is
     `acc.sh ++ a.flatMap boundOf` and its `blks` field is `acc.blks ++ <something independent of
     acc.blks>`.
  2. Conclude `theorem inlineScan_append (fuel) (consts) (sh) (a b) : (Inline.inlineScan (fuel + 1)
     consts sh (a ++ b)).blks = (Inline.inlineScan (fuel + 1) consts sh a).blks ++
     (Inline.inlineScan (fuel + 1) consts (sh ++ a.flatMap Inline.boundOf) b).blks`.
  3. Derive `inline_append` from it: under its hypothesis the extra shadow names are not table
     names, so the second scan equals the scan at `sh` (one induction over the block, using
     `inExpr_keeps_shadowed`, `InlineConstants.lean:407`).
  4. Falsifier: `a := [let X := 1]`, `b := [mstore(X, 0)]`, table `[("X", 7)]`: the unthreaded
     equation (second scan at `sh`) is false; prove the `¬` by `decide`.
- **Deliverable.** `inlineScan_append`, `inline_append` (sorry removed), the falsifier.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.inlineScan_append [propext, Classical.choice,
  Quot.sound] native []`; `grep -c sorry Midfall/LoweringV2/ProgramLemmas.lean` is 0.
- **Stop if.** Step 3 needs a hypothesis `inline_append` does not have: report the block that
  separates them; do not change `inline_append`'s statement.
- **Guidance.** Never unfold `inlineScan` at fuel 64: state everything at `fuel + 1`. Sonnet-only
  split: step 1 / steps 2 and 4 / step 3.

### HLP.1.a — The helper block of every render

GEN · PORT · box 0.5 h · Sonnet · after —

- **Goal.** Land the definition lemmas, which are proved.
- **Needs.** `GeneratorRows.lean`: `kernel_rfl`, `helperBody`, `HelperIs`, `fail_is`,
  `batch_invert_is`, `helpers_are`, `helpers_eq`, `helpers_funDefs`.
- **Does NOT need.** Anything else.
- **VERIFY FIRST.** `check.sh soundness` passes.
- **Do.**
  1. Create `Midfall/LoweringV2/Helpers.lean`; port the eight declarations verbatim.
  2. Add the negative test as a comment with its output: `theorem neg … : (lagInner consts k n
     m).length = 27 := by kernel_rfl` is refused with `(kernel) declaration type mismatch`.
- **Deliverable.** `theorem helpers_eq (R) : R.helpers = [Stmt.funDef "fail" ["sel"] [] (helperBody
  R.consts GenAst.emitFail), …, Stmt.funDef "ec_pairing" ["success", "lhs_mptr", "rhs_mptr"] ["ret"]
  (helperBody R.consts (GenAst.emitEcPairingAt R.pv))]` and the seven `HelperIs` lemmas.
- **Accept.** `#assert_axioms Midfall.LoweringV2.helpers_eq [propext, Classical.choice, Quot.sound]
  native []`; file elaborates in under 30 s; no `maxHeartbeats`.
- **Stop if.** `kernel_rfl` is refused on `helpers_eq` at the tip: `emitHelpers` changed
  (`GenAst.lean:579`); report the diff, do not edit the lemma.
- **Guidance.** Do not replace `kernel_rfl` by `rfl`: the elaborator's `whnf` exceeds the default
  heartbeats on these terms (measured on `lagInner_length`).

### HLP.1.b — batch_invert: the forward pass

SEM · PROOF · box 2.5 h · strongest · after GEN.3, HLP.1.a, T3.9.a

- **Goal.** Close `bi_forward_loop`: the prefix-product loop for a batch of any length.
- **Needs.** `GeneratorRows.lean`: `bi_forward_loop`, `helperBody`, `seg`, `wMulmod`,
  `MemSameOutside`. Emitter `GenAst.lean:499-505`. The loop rule (GEN.3) or
  `ExecLoopAll.countdown_or_halt` (`Midfall/Yul/Contracts.lean:298`). T3.5's `loadWord_storeWord`.
- **Does NOT need.** The modexp call, the backward pass, primality of `r`.
- **VERIFY FIRST.** `check.sh soundness`; `bi_forward_loop` is a sorry; T3.9.a is closed (it is the
  first loop closed with GEN.3 and supplies the script).
- **Do.**
  1. `have hform : seg (helperBody consts GenAst.emitBatchInvertAt) 10 1 = [<the loop>] := by
     kernel_rfl` (the move of `lag_sq_loop_form`).
  2. Invariant with `j` iterations left, `i := (e - a)/32 - 2 - j` done: `mptr = a + 32 + 32 i`,
     `gp_mptr = s + 32 i`, `gp = P i`, scratch words `0..i-1` hold `P 1 .. P i`, the batch window
     unchanged, every word read so far below `r`.
  3. `zero`/`done`: the guard `lt(mptr, sub(mptr_end, 0x20))` is false exactly at `i = (e-a)/32 - 2`
     (`hae`, `he` exclude wrap-around).
  4. `bodyLeave`: the reject arm sets `ret := 0` and leaves: first disjunct of the post.
  5. `progress`: one `mload`, one `mulmod`, one `mstore` at `gp_mptr`; read-over-write with `hdisj`.
  6. `condHalt`, `bodyHalt`, `postHalt`, `bodyBreak`: impossible (no halting builtin, no `break`).
- **Deliverable.** `bi_forward_loop`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.bi_forward_loop [propext, Classical.choice,
  Quot.sound] native []`; no `maxHeartbeats`, no `maxRecDepth`; at most 150 lines.
- **Stop if.** The post's `∃ P` is not what `batch_invert_summary` needs after the last word is
  folded (step outside this card): report the missing conjunct; do not strengthen the pre.
- **Guidance.** The loop's `init` and `post` blocks are empty; the cursor moves inside the body.
  Sonnet-only split: steps 1–3 / 4 and 6 / 5.

### HLP.1.c — batch_invert: the backward pass and the summary

SEM · STATEMENT · box 2.5 h · strongest · after HLP.1.b, T3.5

- **Goal.** State and close the backward loop, then `batch_invert_summary`.
- **Needs.** `GeneratorRows.lean`: `batch_invert_summary`, `BatchInvertPost`. Emitter
  `GenAst.lean:465-542` (statement 29 is the backward loop; statements 15–24 the modexp frame and
  call; statement 5 the single-element arm). `Bridge` modexp facts used by `permissive`
  (`Bridge.lean:731`); `Eip2537` modexp honesty.
- **Does NOT need.** The Lean verifier; `ZMod` beyond one lemma (below).
- **VERIFY FIRST.** HLP.1.b closed; `batch_invert_summary` typechecks.
- **Do.**
  1. State `bi_backward_loop` in the shape of `bi_forward_loop` (bound: batch words minus two);
     invariant: `all_inv` is the inverse of the product of the words not yet recovered, words above
     `mptr` hold their inverses. Land its witness (F1's window: `LAGRANGE_DENOMS_MPTR`, 11 words) and
     falsifier (swap the two body statements).
  2. State and prove the one arithmetic lemma: for prime `r` and `0 < g < r`,
     `wMulmod (modexp g (r - 2) r) g r = 1` (`ZMod.pow_card_sub_one_eq_one`).
  3. Walk the five exits of the body: `success = 0`, reversed range, empty batch, single element,
     general. Each ends in `BatchInvertPost`.
  4. The `staticcall` forks: failed (`precompile_failed = 1`, `ret = 0`) or honest.
- **Deliverable.** `bi_backward_loop`, `batch_invert_summary`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.batch_invert_summary [propext,
  Classical.choice, Quot.sound] native []`; falsifier: with `hrw` dropped the statement is false at
  `rw = 4`, `x = 2` (state it as `¬`).
- **Stop if.** `BatchInvertPost` is false on the empty-batch exit for `succ ∉ {0, 1}`: report (the
  post says `ret ≠ 0 → …` with a vacuous window there; check it first).
- **Guidance.** The two-element tail after the loop is why the loop bound is "words minus two".
  Sonnet-only split: step 1 / step 2 / step 3 exits one to three / exits four and five / step 4.

### SIM.6.a — The model's shape flags under validity

GEN · PROOF · box 1 h · strongest · after RECON.1

- **Goal.** `theorem model_flags_of_valid (R) (hR : R.Valid) : R.model.embeddedVk.isNone = true ∧
  R.model.quotientExternal.isSome = false`.
- **Needs.** `Statements.lean:197` (`Valid.model`), `:130-134` (`embeddedQuotient`, `separateVk`);
  `Midfall/Generator/Artifacts.lean` (`generateVerifierFromPlan`).
- **Does NOT need.** Semantics, the plan's contents.
- **VERIFY FIRST.** `check.sh soundness`; the lemma is a sorry.
- **Do.**
  1. Unfold `generateVerifierFromPlan` to the two record fields; name the two `if`s that set them.
  2. Rewrite with `hR.supported.separateVk` and `hR.supported.embeddedQuotient`; split on the
     `Except` binds that precede the record (`hR.model` says the whole thing is `.ok`).
- **Deliverable.** The lemma, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.model_flags_of_valid [propext,
  Classical.choice, Quot.sound] native []`; witness: `#eval` of the two fields at `poseidonM` prints
  `(true, false)`.
- **Stop if.** A field is set from something other than `R.flags` (then a `Valid` clause is
  missing: PREMISE GAP, report the source line).
- **Guidance.** Do not `simp` with `generateVerifierFromPlan` unfolded globally; use `unfold` once
  and `split`. Sonnet-only split: step 1 / step 2.

### SIM.6.b — The static half of abiHeadOk

ALG · PROOF · box 1 h · strongest · after RECON.1

- **Goal.** `theorem layout_static_of_valid (R) (hR : R.Valid) : R.plan.proofLayout.proofCptr =
  abiVerifyProofProofCptr ∧ R.plan.proofLayout.proofEnd = R.plan.proofLayout.proofCptr +
  R.plan.proofLayout.proofLen`.
- **Needs.** `Statements.lean:192` (`Valid.layout`); `Midfall/Generator/Abi.lean`
  (`ProofCalldataLayout.fromProtocol`).
- **Does NOT need.** Semantics.
- **VERIFY FIRST.** The lemma is a sorry; at F1 `(proofCptr, proofEnd, proofLen,
  abiVerifyProofProofCptr)` prints `(100, 4420, 4320, 100)`.
- **Do.**
  1. Unfold `fromProtocol`; the first conjunct is the constructor's first field.
  2. `proofLen` is defined as a difference or `proofEnd` as a sum: find which, and close by `omega`
     after the `Except` split.
- **Deliverable.** The lemma, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.layout_static_of_valid [propext,
  Classical.choice, Quot.sound] native []`.
- **Stop if.** `proofEnd = proofCptr + proofLen` needs a size bound `fromProtocol` does not check:
  report the counter-layout.
- **Guidance.** Sonnet-only split: one card per conjunct.

### SIM.6.c — The ABI guard

SEM · PROOF · box 2 h · strongest · after GEN.0, OBJ.4, SIM.6.b

- **Goal.** `abi_guard_sem`: every run of the inlined `abiGuardBlock` reverts, or changes nothing
  and `abiHeadOk R.plan.proofLayout cd = true`.
- **Needs.** `GeneratorRows.lean`: `abi_guard_sem`. `Program.lean:66-76`. `SoundnessV3.lean:67`
  (`abiHeadOk`). `Blocks/VkLoading.lean:528` (`vk_ok_calldataload`), `:284` (`vk_nh_binary`). OBJ.4's
  lookup lemmas for `NUM_INSTANCE_CPTR`, `ERR_BAD_CALLDATA_SHAPE`; the model's three ABI numerals
  (`abiSelectorBytes`, `abiProofHeadOffset`, `abiInstancesHeadCptr`).
- **Does NOT need.** Memory, the scope (no call), loops.
- **VERIFY FIRST.** `check.sh soundness`; `(poseidonM.abiSelectorBytes, poseidonM.abiProofHeadOffset,
  poseidonM.abiInstancesHeadCptr)` prints `(4, 64, 36)`.
- **Do.**
  1. Statement-list form by `kernel_rfl` (one `Stmt.cond`).
  2. Guard true: the body is `mstore` then `revert(0, 4)`: `Reverted`.
  3. Guard false: both `eq` hold; turn the two `calldataload`s into `cdWord cd 4` and `cdWord cd
     0x24` (`st.env.calldata = cd.data.toList`); with `hsel` and `layout_static_of_valid` this is
     `abiHeadOk`.
- **Deliverable.** `abi_guard_sem`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.abi_guard_sem [propext, Classical.choice,
  Quot.sound] native []`.
- **Stop if.** The three model numerals are not derivable from `Valid.model` (PREMISE GAP: name the
  field and its source in `Artifacts.lean`).
- **Guidance.** `sub(NUM_INSTANCE_CPTR, 4)` is a word subtraction; `abiHeadOk` compares in `Nat`:
  `proofEnd ≥ 4` and `proofEnd < 2^256` are needed (the second is `ValidV3.cdBound`).

### SIM.6.d — Function definitions execute as a no-op

SEM · PROOF · box 0.5 h · Sonnet · after —

- **Goal.** `theorem funDefs_noop (funs) (b) (hb : ∀ s ∈ b, ∃ n ps rs body, s = Stmt.funDef n ps rs
  body) (V st V' st' o) (h : ExecStmts D funs V st b V' st' o) : V' = V ∧ st' = st ∧ o = .normal`.
- **Needs.** `vendor/yul-semantics/YulSemantics/BigStep.lean` (`Step.funDef`, `seqCons`, `seqStop`);
  `SoundnessV3.lean:1084` (`stmts_append_run`: the induction to copy).
- **Does NOT need.** The EVM dialect.
- **VERIFY FIRST.** The lemma is a sorry; `helpers_funDefs` is proved.
- **Do.**
  1. Induction on `b`; `nil`: `cases h`.
  2. `cons`: `cases h` into `seqCons` / `seqStop`; `cases` the head step (only the `funDef`
     constructor applies); apply the hypothesis to the tail.
- **Deliverable.** The lemma, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.funDefs_noop [propext, Classical.choice,
  Quot.sound] native []`.
- **Stop if.** `Step` has no dedicated `funDef` rule (then definitions are skipped by another rule:
  report its name).

### T3.9.a — Lagrange loop 1: k squarings (first use of the loop rule)

SEM · PROOF · box 2 h · strongest · after GEN.3, T3.8

- **Goal.** Close `lag_sq_loop`, and with it fix the script every later loop card copies.
- **Needs.** `GeneratorRows.lean`: `lag_sq_loop`, `lag_sq_loop_form` (PROVED), `wPow2`, `wMulmod`.
  Emitter `GenAst.lean:692-694`. The loop rule (GEN.3); `Midfall/Yul/Contracts.lean:298`
  (`ExecLoopAll.countdown_or_halt`). `Blocks/VkLoading.lean:553` (`vk_assign_inv`), `:578`
  (`vk_assign_nh`), `:284` (`vk_nh_binary`), `:611` (`vk_get_set_of_some`). T3.8's `wMulmod` =
  `stepOp` lemma.
- **Does NOT need.** Memory, calldata, `ZMod`, the scope.
- **VERIFY FIRST.** `check.sh soundness`; `lag_sq_loop_form` has the standard axioms.
- **Do.**
  1. `rw [lag_sq_loop_form]`; `simp only [Blocks.VkLoading.vkSite, hr]` turns the `r` site into
     `Expr.var "r"`.
  2. Invert the one-statement list and the `forLoop` to its init block (`let idx := 0`) and an
     `ExecLoop`.
  3. Rule instance: `Inv j V st := st = st₀ ∧ VEnv.get V "idx" = some (ofNat (k - j)) ∧ VEnv.get V
     "x_n" = some (wPow2 rw (k - j) x) ∧ <the other bindings of V₀ unchanged> ∧ j ≤ k`.
  4. `zero` and `done`: `lt(idx, k)` is zero iff `idx = k` (uses `hk`).
  5. `progress`: `vk_assign_inv` on the body, then on the post; `wPow2` unfolds one step.
  6. The five halt/leave/break premises: no such builtin, no such statement.
  7. Exit: the loop's scope drops `idx`; `V' = VEnv.set V "x_n" (wPow2 rw k x)`.
- **Deliverable.** `lag_sq_loop`, sorry-free; a paragraph in the report: which step took longest.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.lag_sq_loop [propext, Classical.choice,
  Quot.sound] native []`; at most 120 lines; falsifier: the statement with `hk` dropped is false at
  `k = 2^256` (state the `¬` on a one-element environment).
- **Stop if.** The loop rule cannot express the scope exit of the `init` binder (`idx`): report to
  GEN.3's owner; do not hand-roll a second rule.
- **Guidance.** `wPow2 r (j+1) x = wPow2 r j (wMulmod x x r)` recurses on the INPUT; the invariant
  needs the other orientation: prove `wPow2 r (j+1) x = let y := wPow2 r j x; wMulmod y y r` first.
  Sonnet-only split: steps 1–2 / 3–4 / 5 / 6–7.

### T3.9.b — Lagrange loop 2: the denominators

SEM · PROOF · box 2 h · Sonnet · after T3.9.a, T3.5

- **Goal.** Close `lag_denoms_loop` (bound `n + m`).
- **Needs.** `GeneratorRows.lean`: `lag_denoms_loop`, `omegaPows`, `wAddmod`, `MemSameOutside`.
  Emitter `GenAst.lean:700-705`. T3.9.a's script. T3.5's `loadWord_storeWord`.
- **Does NOT need.** The scope, calldata.
- **VERIFY FIRST.** T3.9.a closed; the lemma is a sorry.
- **Do.**
  1. Statement form by `kernel_rfl` (statement 7); the `OMEGA_INV_TO_L_MPTR` site by `hL`.
  2. Init block: `pow_of_omega := mload(aL)`.
  3. Invariant with `j` left, `i := n + m - j`: `mptr = D + 32 i`, `pow_of_omega = omegaPows rw om
     w0 i`, words `0..i-1` of the window hold the stated values, memory outside unchanged.
  4. `progress`: one `mstore` at `mptr`, one `mulmod`; `loadWord_storeWord` for the words already
     written.
  5. Exit: `mptr = mptr_end`; no wrap by `hD`.
- **Deliverable.** `lag_denoms_loop`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.lag_denoms_loop [propext, Classical.choice,
  Quot.sound] native []`; at most 150 lines.
- **Stop if.** The post needs `st'.activeWords` (it does not mention it): report which consumer.
- **Guidance.** The value written is `addmod(x, sub(r, pow), r)`: `sub` is a word subtraction, as
  in the statement (`rw - …`).

### T3.9.c — Lagrange loop 3: inverses to Lagrange values

SEM · PROOF · box 1.5 h · Sonnet · after T3.9.b

- **Goal.** Close `lag_second_pass_loop` (bound `n + m`).
- **Needs.** `GeneratorRows.lean`: `lag_second_pass_loop`. Emitter `GenAst.lean:718-725`.
  T3.9.b's proof (same window, same walk).
- **Does NOT need.** The scope, calldata.
- **VERIFY FIRST.** T3.9.b closed.
- **Do.**
  1. Statement form (statement 13).
  2. Copy T3.9.b's invariant; the body reads the word it overwrites, so the invariant also says
     words `i..` are still the input words.
  3. `hLD` keeps the `OMEGA_INV_TO_L` word out of the window.
- **Deliverable.** `lag_second_pass_loop`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.lag_second_pass_loop [propext,
  Classical.choice, Quot.sound] native []`.
- **Stop if.** More than 1.5 h: report the step; do not change T3.9.b.

### T3.9.d — Lagrange loop 4: l_blind

SEM · PROOF · box 1 h · Sonnet · after T3.9.a

- **Goal.** Close `lag_lblind_loop` (bound `m − 2`, no memory write).
- **Needs.** `GeneratorRows.lean`: `lag_lblind_loop`, `wSum`. Emitter `GenAst.lean:729-733`.
- **Does NOT need.** Read-over-write.
- **VERIFY FIRST.** T3.9.a closed.
- **Do.**
  1. Statement form (statement 16); the `LAGRANGE_DENOMS_MPTR` site by `hDn`.
  2. Invariant: `l_i_cptr = D + 64 + 32 i`, `l_blind = wSum rw f i lb`.
  3. Exit at `i = m - 2` (`hm`, `hD`).
- **Deliverable.** `lag_lblind_loop`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.lag_lblind_loop [propext, Classical.choice,
  Quot.sound] native []`; falsifier: with `hm` dropped the statement is false at `m = 1` (the
  cursor stays at `D + 64`, the post says `D + 32`).
- **Stop if.** —

### T3.9.e — Lagrange loop 5: the instance polynomial

SEM · PROOF · box 1.5 h · Sonnet · after T3.9.a

- **Goal.** Close `lag_instance_loop` (bound `n`, two cursors, `calldataload`).
- **Needs.** `GeneratorRows.lean`: `lag_instance_loop`. Emitter `GenAst.lean:738-746`.
  `Blocks/VkLoading.lean:528` (`vk_ok_calldataload`); `Lowering/Calldata.lean:279` (`cdWord`).
- **Does NOT need.** Memory writes.
- **VERIFY FIRST.** T3.9.a closed.
- **Do.**
  1. Statement form (statement 18); the `INSTANCE_CPTR` site by `hI`.
  2. Init block binds two variables; the post block has two assignments.
  3. Invariant: both cursors at offset `32 j`, `instance_eval = wSum … j 0`.
  4. `calldataload(aI + 32 j) = cdWord cd (aI + 32 j)` from `st.env.calldata = cd.data.toList`.
- **Deliverable.** `lag_instance_loop`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.lag_instance_loop [propext,
  Classical.choice, Quot.sound] native []`.
- **Stop if.** `calldataload` past the end of calldata is not `cdWord` (zero padding differs):
  report the two definitions; the statement may need `aI + 32 n ≤ cd.size`.

### T3.9.g — The Lagrange word relation is the verifier's Lagrange step

ALG · PROOF · box 2.5 h · strongest · after T3.8

- **Goal.** Close `lag_agrees`: no Yul.
- **Needs.** `GeneratorRows.lean`: `LagRel`, `LagWords`, `lag_agrees`. `Lowering/Snapshot.lean:230`
  (`snapshotLagrangeStep`), `:217` (`instanceEvalOf`); `Halo2/Exec/Verifier.lean:245`
  (`lagrangeTriple`); `Inv.lean:533` (`EnvAgrees`: `domainN`, `baryWeight`, `omegaInvMul`,
  `omegaOrder`, `negLagranges`, `modulus`); `Lowering/Qvm.lean:143-169` (the `mulmod`/`addmod`
  homomorphism lemmas to copy for `frWord`).
- **Does NOT need.** Semantics, memory, the scope.
- **VERIFY FIRST.** `check.sh soundness`; `snapshotLagrangeStepKats_ok` (`Snapshot.lean:519`) still
  evaluates to `true`.
- **Do.**
  1. `frWord` homomorphism: `wMulmod (frWord a) (frWord b) (ofNat p) = frWord (a * b)`, the same for
     `wAddmod`, and `ofNat p - frWord a` under `addmod` is negation.
  2. `wPow2` is `x ^ (2 ^ k)`; `omegaPows` at `w0 = ω⁻ᴸ` is `ω^(i - L)`.
  3. The inverses in `LagRel` are unique (prime modulus), so `inv i = frWord (x - ω^(i-L))⁻¹`.
  4. `L i` is the Lagrange basis value at rotation `i - L` (barycentric formula, `baryWeight`,
     `domainN`).
  5. Match the four outputs with `lagrangeTriple` and `instanceEvalOf` (uses `hm`).
- **Deliverable.** `lag_agrees`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.lag_agrees [propext, Classical.choice,
  Quot.sound] native []`; falsifier: at a toy key over `Fr 17` with `numNegLagranges = 1`, an
  instance of `LagRel` whose `lBlind` differs from the verifier's (`#eval`), showing `hm` is used.
- **Stop if.** `lagrangeTriple`'s `l_blind` range and `LagRel`'s `(L 1 … L (m-1))` differ by one
  term: report both sums; do not edit `LagRel`.
- **Guidance.** `hxn` is supplied by the caller from `EnvAgrees.domainN`. Sonnet-only split: step 1
  / 2 / 3 / 4 / 5.

### T3.9.h — Lagrange: the poisoned half

SEM · PROOF · box 1.5 h · Sonnet · after HLP.1.c, T3.9.a–e

- **Goal.** Close `lag_poison`: from `success = 0` every run reverts.
- **Needs.** `GeneratorRows.lean`: `lag_poison`, `batch_invert_summary` (its `succ = 0` clause),
  `fail_is`, `batch_invert_is`. `Blocks/VkLoading.lean:449` (`vk_fail_reverts`), `:467`
  (`vk_guard_fires`).
- **Does NOT need.** Any value the loops compute (use the loop lemmas only for "ends normally").
- **VERIFY FIRST.** HLP.1.c closed.
- **Do.**
  1. Walk the inner block: each loop ends normally (T3.9.a–e, posts discarded).
  2. The call returns `(0, 0)`: `success = 0`, `lagrange_precompile_failed = 0`.
  3. Last statement: outer guard fires, inner guard does not, `fail(ERR_PROOF_REJECTED)` reverts.
- **Deliverable.** `lag_poison`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.lag_poison [propext, Classical.choice,
  Quot.sound] native []`.
- **Stop if.** A loop lemma's precondition is not available at a poisoned boundary (memory is
  arbitrary there): report which one; the loops' termination must not depend on memory.

### ROW.TP.1 — A walk loop is constant-free

GEN · PROOF · box 1 h · Sonnet · after GEN.4

- **Goal.** `theorem inline_g1WalkLoop (fuel) (consts) (sh) (walk) (bytes) (hw : Inline.shadowed sh
  walk = true) (hp : Inline.shadowed sh "proof_cptr" = true) (hb : Inline.shadowed sh "buf_len" =
  true) : (Inline.inlineScan (fuel + 2) consts sh [GenAst.g1WalkLoop walk bytes]).blks =
  [GenAst.g1WalkLoop walk bytes]`.
- **Needs.** `InlineConstants.lean:287-372`; `GenAst.lean:1011-1024`;
  `inExpr_keeps_shadowed` (`InlineConstants.lean:407`).
- **Does NOT need.** Semantics.
- **VERIFY FIRST.** The lemma is a sorry.
- **Do.**
  1. Unfold one level of `inlineScan`/`inlineStep`/`inlineStmtStep` at the `forLoop`.
  2. The init block binds `end`; the shadow list for cond, post and body is `sh ++ ["end"]`.
  3. Each of the eleven variable sites is shadowed: rewrite with `inExpr_keeps_shadowed`.
- **Deliverable.** The lemma, sorry-free; the same for `g1WalkBody` and `g1AbsorbCopy`.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.inline_g1WalkLoop [propext,
  Classical.choice, Quot.sound] native []`.
- **Stop if.** `shadowed (sh ++ ["end"]) x` does not reduce from `shadowed sh x = true`: prove
  `shadowed_append_left` first (three lines) and continue.

### ROW.TP.2 — The walk loop, one lemma for six sections

SEM · PROOF · box 2.5 h · strongest · after GEN.3, ROW.TP.3, T3.5

- **Goal.** Close `g1walk_loop_sem` (bound `j`, the section's frame count).
- **Needs.** `GeneratorRows.lean`: `g1walk_loop_sem`. Emitter `GenAst.lean:1011-1024`. The
  `common_uncompressed_g1` summary (ROW.TP.3). `SoundnessV3.lean:481` (`cdSlice`);
  `Lowering/Calldata.lean:288` (`g1WordsOk`). T3.9.b's script (memory-writing loop).
- **Does NOT need.** The Lean transcript; keccak.
- **VERIFY FIRST.** ROW.TP.3's `common_uncompressed_g1` summary is closed; T3.9.b closed.
- **Do.**
  1. Init binds `end := proof_cptr + 128 j` (no wrap: `ha`, `hcd`).
  2. Invariant with `i` frames done: three cursors at `+128 i`; buffer and walk windows hold
     `cdSlice cd a (128 i)`; `g1WordsOk` for frames `< i`; memory outside both windows unchanged.
  3. Body: the helper call (summary: reverts, or absorbs 128 bytes and the frame passed the range
     check), `calldatacopy` to the walk, two cursor steps.
  4. `bodyHalt`: the helper's revert is the first disjunct of the post.
  5. Exit at `i = j`.
- **Deliverable.** `g1walk_loop_sem`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.g1walk_loop_sem [propext, Classical.choice,
  Quot.sound] native []`; falsifier: with `hdisj` dropped, overlapping windows make the buffer
  conjunct false (state on a two-frame toy).
- **Stop if.** The range check of the helper and `g1WordsOk` are not the same inequality: report
  both; this is fault-table row 9.
- **Guidance.** `cdSlice` does not pad; `ha` keeps every read inside the calldata. Sonnet-only
  split: steps 1–2 / 3 / 4–5.

### ROW.TP.6 — The parser's read schedule is the layout's slot list

ALG · PROOF · box 2 h · strongest · after OBJ.7

- **Goal.** `theorem tp_events_slots (R) (hR : R.Valid) : R.tpEvents.filterMap TEv.slot? =
  (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots`.
- **Needs.** `GeneratorRows.lean`: `tpEvents`, `TEv.slot?`, `tp_events_slots`;
  `GeneratorRowsWitness.lean`: `tp_events_slots_F1`, `tp_events_slots_falsifier`.
  `Lowering/Inv.lean:302` (`parserFactsOfPlan`); `Lowering/Calldata.lean`
  (`RepackedProofLayoutPlan.fromProofLayout`); `Generator/Artifacts.lean` (where `userPhases` and
  `lookupHPlusAcc` are computed).
- **Does NOT need.** Semantics.
- **VERIFY FIRST.** The witness file's two theorems still hold.
- **Do.**
  1. Write `fromProofLayout … .slots` as a concatenation of ten sections (one `simp` lemma).
  2. Section by section: `filterMap` of a `tpWalk` is `replicate (bytes/128) .g1`; of the squeezes,
     nothing.
  3. Match each section's count with the layout's `itemCount`, using what `Valid.model` gives about
     `parserFactsOfPlan` (PG-PARSER).
- **Deliverable.** The lemma, or the exact list of facts `Valid` does not supply.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.tp_events_slots [propext, Classical.choice,
  Quot.sound] native []`.
- **Stop if.** Step 3 needs a fact about `generateVerifierFromPlan` nobody has stated: that is
  PG-PARSER. Write it as one lemma statement with its F1 witness and stop; do not add a hypothesis.
- **Guidance.** Byte lengths divisible by 128 (or 32) come from `ProofSection`'s constructor.
  Sonnet-only split: step 1 / step 2 / step 3 per section group.

### ROW.TP.7 — The parser computes TpPost

SEM · PROOF · box 2.5 h · strongest · after ROW.TP.1–6, GEN.1

- **Goal.** Close `tp_computes` from the fold lemma (ROW.TP.5) and the loop lemmas.
- **Needs.** `GeneratorRows.lean`: `tp_computes`, `TpPost`, `XcriptSlots`. `SoundnessV3.lean:506`
  (`MirrorAt`), `:107` (`rawDecode`), `:255` (`snapshotXcriptRun`). `Yul/Bridge.lean:451`
  (`hashOfBytes_readBytes`).
- **Does NOT need.** Point validity.
- **VERIFY FIRST.** ROW.TP.5 closed.
- **Do.**
  1. From the fold: `MirrorAt` (each walk window is its calldata section) and
     `rawDecode … isSome` (each frame passed `g1WordsOk`, each scalar `< r`, the cursor ended at
     `NUM_INSTANCE_CPTR`: `tp_events_slots`).
  2. `XcriptSlots`: for a decoding, the buffer bytes at each squeeze are the Lean transcript's
     (`SimPins.eipRt` turns a frame into `toEip` of its point; `toEipOne` the committed instance).
  3. `BaseInv .transcript` and `Frame`: unchanged memory outside the parser's windows.
- **Deliverable.** `tp_computes`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.tp_computes [propext, Classical.choice,
  Quot.sound] native []`.
- **Stop if.** Step 2 needs the Lean prefix to EXIST (it is a hypothesis of `XcriptSlots`, not a
  goal): if a goal of that form appears, the statement was misread.
- **Guidance.** Step 2 is the "one lemma used five times" of the old card; state it once per
  squeeze kind. Sonnet-only split: step 1 Mirror / step 1 rawDecode / step 2 / step 3.

### ROW.TP.8 — TpPost is the staged boundary

ALG · PROOF · box 2 h · strongest · after SIM.10

- **Goal.** Close `tp_agrees`: `TpPost R H vkAddr cd V st → StageInv R H vkAddr cd .transcript V st`.
- **Needs.** `GeneratorRows.lean`: `tp_agrees`. `SoundnessV3.lean`: `xcript_total` (:1354),
  `padSnap` (:270), `leanStage` (:336), `Agree` (:532). `Inv.lean:725` (`.transcript` clauses
  :757-776).
- **Does NOT need.** Semantics.
- **VERIFY FIRST.** SIM.10 closed.
- **Do.**
  1. For a decoding, `xcript_total` gives `x`; `leanStage … .transcript = .ok (padSnap x …)`.
  2. `Inv .transcript` clause by clause with `if_pos`/`if_neg` on the checkpoint guards: ten
     `holdsFr` from `XcriptSlots`; four `holdsG1(s)` from `MirrorAt` and `eipRt`; the cursor word
     from `MirrorAt.qEvalCptr`; the `.vk` clauses from `BaseInv`.
- **Deliverable.** `tp_agrees`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.tp_agrees [propext, Classical.choice,
  Quot.sound] native []`; no `maxHeartbeats`.
- **Stop if.** Normalising `InvAt` as a whole (measured to exceed the default heartbeats,
  `Blocks/VkLoading.lean:710`): assemble clause by clause instead.

### ROW.TP.9 — The parser: the poisoned half

SEM · PROOF · box 1.5 h · Sonnet · after ROW.TP.2, ROW.TP.4

- **Goal.** Close `tp_poison`.
- **Needs.** `GeneratorRows.lean`: `tp_poison`. `Blocks/VkLoading.lean:631` (`vk_poison_step`: an
  `and(success, …)` assignment keeps `success = 0`), `:467` (`vk_guard_fires`), `:449`.
- **Does NOT need.** Any computed value.
- **VERIFY FIRST.** The loop lemmas are closed.
- **Do.**
  1. No statement but the instance loop's `success := and(success, …)` assigns `success`:
     `vk_poison_step`.
  2. Every other statement ends normally or reverts.
  3. The last statement reverts.
- **Deliverable.** `tp_poison`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.tp_poison [propext, Classical.choice,
  Quot.sound] native []`.
- **Stop if.** A loop lemma's precondition fails at a poisoned boundary: report it.

### ROW.Q.1 — The linearization loop

SEM · PROOF · box 1.5 h · Sonnet · after T3.9.a

- **Goal.** Close `qlin_split_loop` (bound `k`), then the nine-statement scope.
- **Needs.** `GeneratorRows.lean`: `qlin_slice`, `qlinInner`, `qlinInner_length`, `wSplit`,
  `qlin_split_loop`. Emitter `GenAst.lean:840-864`. T3.9.a's script.
- **Does NOT need.** The numerator, memory inside the loop.
- **VERIFY FIRST.** T3.9.a closed; `qlinInner_length` proved.
- **Do.**
  1. Statement form of statement 4 by `kernel_rfl`.
  2. Invariant: `(x_pow_2i_minus1, x_pow_2i) = wSplit rw x (k - j)`. The body's first assignment
     reads the old `x_pow_2i`.
  3. After the loop: two `mstore`s at `QUOTIENT_MPTR` and `+ 0x20`.
- **Deliverable.** `qlin_split_loop`, sorry-free, and the scope's contract.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.qlin_split_loop [propext, Classical.choice,
  Quot.sound] native []`; falsifier: the body's two assignments swapped give a different `wSplit`
  (`#eval` at `k = 2`).
- **Stop if.** —

### ROW.Q.6 — qvm_compile_correct_identity

ALG · PROOF · box 2.5 h · strongest · after —

- **Goal.** Close `Lowering/Qvm.lean:619-631` for the plain cases; issue one card per peephole.
- **Needs.** `Lowering/Qvm.lean`: `RecognizersSound` (:535), `exprBounded` (:575),
  `evalQuotientExpr_memOfρ` (:334), `NoMiss_evalQuotientExpr_memOfρ` (:435), `derive_hit` (:238),
  the per-arm facts (:1197, :1864, :2588), `evalQuotientIdentityLoop_fuelNeverBinds` (:1481);
  `Generator/Quotient/VmBuilder.lean:700-894` (`identityExpr`, about 40 panic sites).
- **Does NOT need.** Yul, the render, the fold.
- **VERIFY FIRST.** `lake env lean Midfall/Lowering/Qvm.lean` has the five sorries at the lines
  above; `arms_agreement_hypotheses_satisfiable` (:1436) still proved.
- **Do.**
  1. State the builder invariant: after emitting `e` from `s₀`, the new bytes run from any stack
     to that stack with the value of `e` pushed (existential in the returned memory, as the
     statement already is).
  2. Prove it for `const`, `mem`, `add`, `mul`, `neg` with no recognizer firing, by induction on the
     emitter's fuel.
  3. State the four peephole cases as lemmas under `hr`; leave them as named sorries.
  4. Derive the theorem from steps 2–3 and `compactQuotientRuns`/`finalizedIdentitySegment`.
- **Deliverable.** The invariant, the plain cases proved, four named leaves, the theorem derived.
- **Accept.** `#assert_axioms Midfall.Lowering.qvm_compile_correct_identity [propext,
  Classical.choice, Quot.sound] native []` once the four leaves close; today `#cone_sorries` lists
  exactly the four.
- **Stop if.** The run-compaction step changes the value on some byte pattern: land the
  counterexample (NEGATIVE).
- **Guidance.** State everything on `qvmBytesToNats build.bytes` (post-finish), never on the
  builder's `s.bytes`. Sonnet-only split: step 1 / step 2 per constructor / step 3 / step 4.

### ROW.PCS.2 — PCS block 2: the x1 power table

SEM · PROOF · box 1.5 h · Sonnet · after T3.9.b

- **Goal.** Close `pcs_b2_sem` (bound `nb − 1`; no loop when `nb ≤ 1`).
- **Needs.** `GeneratorRows.lean`: `pcs_b2_sem`, `wPowers`. Emitter `GenAstPcs.lean:163-176`.
  T3.9.b's script.
- **Does NOT need.** The scope, calldata.
- **VERIFY FIRST.** T3.9.b closed.
- **Do.**
  1. Case `nb ≤ 1`: two statements, by GEN.0's execution.
  2. Case `nb > 1`: invariant `p = aP + 32 i`, `acc = (wPowers rw x1 trunc i).1`, words `0..i` hold
     the stored values; the body advances `p` before the store.
  3. Both arms of `trunc` at once: the stored word is `(wPowers …).2`.
- **Deliverable.** `pcs_b2_sem`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.pcs_b2_sem [propext, Classical.choice,
  Quot.sound] native []`.
- **Stop if.** The inlined block is not a function of the table at the sites `X1_MPTR`,
  `X1_POWERS_MPTR`, `r` only: report the extra site.

### ROW.PCS.9 — A raw walk with valid frames decodes

ALG · PROOF · box 1 h · Sonnet · after SIM.1

- **Goal.** `theorem decode_exists (R) (cd) (raw) (instW) (hraw : rawDecode (p := p)
  R.plan.proofLayout R.cfg.numInstances cd = some (raw, instW)) (hpts : ∀ b, RawMsg.g1 b ∈ raw →
  (R.E.g1.ofEip? b).isSome = true) : ∃ ms instW' inst, Decoded R cd ms instW' inst`.
- **Needs.** `SoundnessV3.lean:197` (`decodeCalldata_isSome_iff`, proved), `:118` (`liftRaw`),
  `:107` (`rawDecode`: its last guard is `inst.all (· < p)`); `Shared.lean:106` (`instOfWords?`).
- **Does NOT need.** Semantics.
- **VERIFY FIRST.** `rawDecodeAgreesKats_ok` (`SoundnessV3.lean:1400`) evaluates to `true`.
- **Do.**
  1. `raw.mapM (liftRaw c)` is `some` when every `g1` frame decodes: induction on `raw`.
  2. `decodeCalldata_isSome_iff` gives `ms`.
  3. `instOfWords? instW = some inst` from `rawDecode`'s last guard.
- **Deliverable.** `decode_exists`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.decode_exists [propext, Classical.choice,
  Quot.sound] native []`; falsifier: `hpts` dropped is false on the KAT's last case (raw-ok,
  decode-none).
- **Stop if.** `decodeCalldata` returns words other than `rawDecode`'s (`instW' ≠ instW`): keep the
  existential, report.

### TOT.1.a — A program without gas() runs the same under every gas oracle

SEM · PROOF · box 2.5 h · strongest · after —

- **Goal.** `theorem runBody_gas_oblivious (R) (vkAddr) (hgas : GasFree (R.prog vkAddr 0)) (c)
  (g g') (st₀) (obs) (h : RunBody R vkAddr 0 c g st₀ obs) : RunBody R vkAddr 0 c g' st₀ obs`.
- **Needs.** `GeneratorRows.lean`: `gasFreeScan`, `GasFree`. `Yul/Bridge.lean:1221`
  (`Run_worldEq_of_noWriters`: the `Step` induction to copy), `:1100` (`noWritersScan`: the scan
  whose monotonicity lemmas to copy). `EVMExec.lean` (`builtinWithExternal`: the one place the
  oracle is read).
- **Does NOT need.** The render beyond `R.prog`; any block.
- **VERIFY FIRST.** The two `decide` examples after `GasFree` still pass.
- **Do.**
  1. Generic statement: for a block `b` with `GasFree b` and a function environment all of whose
     bodies are gas-free, a `Step` derivation at `Bridge.Dialect c g` is one at `Bridge.Dialect c
     g'` (same environments, states, outcome).
  2. Mutual induction on `Step`; the only case that mentions `g` is the `gas` builtin, excluded by
     the scan.
  3. The scope: `hoist` of a gas-free block has gas-free bodies (the scan descends into `funDef`).
  4. Specialise to `RunBody`.
- **Deliverable.** The generic lemma and `runBody_gas_oblivious`, sorry-free.
- **Accept.** `#assert_axioms Midfall.LoweringV2.V3.Gen.runBody_gas_oblivious [propext,
  Classical.choice, Quot.sound] native []`; falsifier: `[pop(gas())]` has a run at `ofFun 0` and
  none at `ExternalGas.none`.
- **Stop if.** `Run_worldEq_of_noWriters` is still a sorry and its induction scheme does not exist:
  write the scheme once here and say so; SIM.5 then reuses it.
- **Guidance.** The two dialects have the same `Value` and `State`; the statement transports the
  derivation, not an equality of types. Sonnet-only split: step 1 / step 2 expressions / step 2
  statements / steps 3–4.

## Area WID — widening the class to the IVC verifier  **[D-P72, signed 2026-11-17: scope and clauses 1–10]**

Milestone M9 of PLAN-V3 §5 (20 cards: WID.1–WID.9 without a WID.10, WID.11–WID.17, WID.19, WID.H, GEN.2, RECON.3). The generator theorem is widened, **for every render**, to accumulator
mode with the batched final pairing and to the external quotient evaluator. Nothing here is proved
at the IVC circuit: F2 (the IVC decider circuit, k = 20) is a test fixture. Evidence, all
typechecked by `bash docs/plans/V3-evidence/check.sh widening`:
`lean/widening/WideningV3.lean` (scope, reference, evaluator trust, headline),
`WideningStages.lean` (stage invariants and row families), `WideningTests.lean` (decoder tests on
the tracked instance words), `IvcPartials.lean` (seven partials rendered byte for byte); memos
`design/ivc-widening.md` and `design/ivc-object-reference.md`.

**Readiness.** D-P72 is signed in full, so a WID card is READY when its `after` cards are merged.
WID.2 depends on nothing and may run now. Row cards (WID.13–WID.19) are SKELETON cards: each
issues its PROOF children in the pattern its base-class row established in M6, so none is briefed
before that row is merged.

**Names used below** (line numbers at the commit that added this area; find a declaration by
name; V = `WideningV3.lean`, S = `WideningStages.lean`): `SupportedW` V:104, `AccShape` V:83, `ExternalPinned` V:93, `LeanAcceptsAcc` V:166, `leanAcceptsAcc_of_rust` V:241, `rust_or_collision_of_leanAcceptsAcc` V:272, `alpha_atMostOne` V:297, `EvalObject` V:314, `EvalEntry` V:326, `EvaluatorTrust` V:389, `callsW` V:447, `LoweringEquivalenceW` V:532, `lowering_equivalenceW_of` V:604, `equivalenceW_iff_V3` V:637, `HypothesesInhabitedW` V:704, `PairingInputsAgree` V:737, `ValidW` V:800, `model_quotientMode` V:808, `AccInv` S:150, `leanStageW` S:171, `StageInvW` S:317, `stageInvW_iff_V3` S:329, `stageInv_false_of_acc` S:230, `EvalBodyShape` S:438, `EvalBodyAgree` S:463, `EvalBodyTotal` S:483, `EvalContracts` S:491, `BatchedInv` S:517, `batchedCheck_iff_contract` S:532, `BlockSimW` S:555, `SimContractsW` S:569, `BlockProgSW` S:588, `ProgContractsW` S:601, `lowering_correctW` S:652, `lowering_correct_of_W` S:698, `lowering_correctW_needs_evalContracts` S:663.

### WID.1 — Land the widening statements (no frozen edit)

> **Not a registered sorry:** `lowering_correctW` is stated with the evaluator's contract as a hypothesis (`hQ : isExternal R → EvalContracts R Q`); without it the statement is false (an empty evaluator body). WID.6 ties `Q` to the generated body, WID.17 proves `EvalContracts`, WID.H drops `hQ`. `ValidCore` is stated over the 18-clause `ValidV3` of `StatementsV3.lean`; after RECON.1 it is restated over the single text (RECON.1b).


INFRA · PORT · box 2 h · Sonnet · after ST.1, SIM.1, SIM.2

- **Goal.** The three widening files compile in the tree as `Midfall/LoweringV3/Widening.lean`,
  `WideningStages.lean` and `Midfall/Instances/WideningTests.lean`, with their four open
  obligations registered.
- **Needs.** `docs/plans/V3-evidence/lean/widening/{WideningV3,WideningStages,WideningTests}.lean`;
  the modules ST.1 and SIM.1 landed (they replace `import StatementsV3` / `import SoundnessV3`).
- **Does NOT need.** Any proof; the IVC artifact; any Rust.
- **VERIFY FIRST.** `bash docs/plans/V3-evidence/check.sh widening` prints four `ok` lines with
  1, 3, 0, 0 sorry warnings.
- **Do.**
  1. Copy the three files verbatim; change only the two import lines and the module names.
  2. `lake build`; fix name resolution only (no statement edits).
  3. Register the four sorries in the sorry register with these names: `lowering_correctW`,
     `model_quotientMode`, `instWords_of_decoded`, `batchedCheck_iff_contract`.
  4. Add `#print axioms` for `equivalenceW_iff_V3`, `lowering_equivalenceW_of`,
     `leanAcceptsAcc_of_rust`, `rust_or_collision_of_leanAcceptsAcc`, `alpha_atMostOne`.
- **Deliverable.** The three modules; the register rows.
- **Accept.** The five `#print axioms` lines print the standard three only; `WideningTests`'s five
  `#eval` print `true`; `verify.sh --quick` green; `Frozen.sha256` unchanged.
- **Stop if.** A statement stops elaborating against the landed V3 modules: report the first
  error; do not restate.
- **Guidance.** The namespace is `Midfall.LoweringW`. `accTable` and `accBases` are empty arrays on
  purpose (clause 2: no fixed-base tail).

### WID.2 — KAT: the ported partials render the IVC verifier byte for byte

GEN · KAT · box 1 h · Sonnet · after —

- **Goal.** A gate that the seven template partials the Lean generator ports occur exactly once
  each in the tracked IVC `Halo2Verifier.sol`, so that a regression in accumulator or
  external-evaluator rendering is caught before any bundle exists.
- **Needs.** `docs/plans/V3-evidence/lean/widening/IvcPartials.lean`;
  `Midfall/Generator/VerifierPartials.lean` (`VerifierPartialKats`);
  `proofs/solidity-verifier/target/ivc-keccak-solidity-dump/Halo2Verifier.sol` (tracked).
- **Does NOT need.** The constraint system of the decider; any proof.
- **Do.**
  1. Move the file to `Midfall/Generator/IvcPartialKats.lean`; turn each printed line into a
     `Bool` definition (`occurs exactly once ∧ includes the region boundary`).
  2. Annotate each with `-- expect true` in the form `kat_gate.py` counts, and bump the pinned
     count with provenance (as DG.0 did).
  3. Add one negative control: the F1-context AccumulatorHelpers render does NOT include the
     boundary (the file's last line already measures it).
- **Deliverable.** The KAT module; the gate count updated.
- **Accept.** `checks.sh` green; the seven lines are `true`, the control is `false` and annotated
  as such.
- **Stop if.** A partial occurs zero or two times: that is a port divergence; report the partial
  and the first differing line, change nothing in the generator.
- **Guidance.** The context values are read from the artifact by hand in the evidence file
  (advice 15, two lookups, six permutation sets, 16 instances, k = 20); WID.5 replaces them by the
  exported key.

### WID.3 — Exporter for the decider key (production SRS, no proof)

INFRA · PORT · box 2.5 h · Sonnet · after REF.11

- **Goal.** `formal/fixtures/conformance/ivc/{vk.json,cs.json,params.json,build.json}` for the IVC
  decider circuit, in REF.11's schema 2, so that the Lean generator can be run on a real
  accumulator-mode, external-evaluator key.
- **Needs.** `proofs/solidity-verifier/tests/conformance_export.rs`
  (`export_poseidon_conformance_bundle`); `proofs/solidity-verifier/tests/ivc_keccak_solidity.rs`
  (`ivc_final_keccak_solidity_e2e` :950: how the decider relation, `decider_vk` and the generator
  options are built; `load_decider_srs` :732; env `HALO2_SOLIDITY_RUN_IVC_BENCH`);
  `zk_stdlib/examples/assets/midnight-srs-2p19` and `-2p20` (present; do not download).
- **Does NOT need.** A proof of the decider circuit; the Lean side; any change under `proofs/src`.
- **VERIFY FIRST.** Both SRS files exist; pinned solc 0.8.30 is on the path
  (`pinned_solc_available`).
- **Do.**
  1. Factor the F1 exporter's serialisers so they take any `VerifyingKey` and `ConstraintSystem`.
  2. Add `export_ivc_decider_conformance_bundle`, gated by the same env var and features
     (`evm,truncated-challenges,in-circuit-fewer-point-sets`): build the IVC key (k = 19) and the
     decider key (k = 20) exactly as the e2e test does, and write the decider's key, constraint
     system, generator options (accumulator encoding, external quotient) and the three rendered
     `.sol` files.
  3. Write `manifest.sha256`; record the command and its wall-clock time in `build.json`.
- **Deliverable.** The bundle directory and the exporter test.
- **Accept.** The exported `Halo2Verifier.sol`, `Halo2QuotientEvaluator.sol` and
  `Halo2VerifyingKey.sol` are byte-identical to the tracked ones in
  `target/ivc-keccak-solidity-dump/` (`cmp`); `sha256sum -c manifest.sha256` passes.
- **Stop if.** The rendered files differ from the tracked ones: report the first differing line of
  each; the tracked files were committed from another machine on 2026-10-23 and may be stale.
- **Guidance.** Key generation alone needs no proving; the full e2e trace run was measured at
  602 s. Run under `--release`. The dump's `proof.bin`, `calldata.bin` and `contract-sizes.txt`
  are untracked leftovers of another render: do not use them.

### WID.4 — Test fixture F2 under one seeded test SRS (D-P72 clauses 7, 8)

> **Order.** If the evaluator's free-memory guard (D-P72 clause 9) is added to the template, the rendered evaluator and its pinned code hash change: run this card after the guard has landed, or re-run it then (the bundle is one run, pinned by its manifest).


INFRA · PORT · box 2.5 h · Sonnet · after WID.3

- **Goal.** A second bundle `formal/fixtures/conformance/ivc-testsrs/` with a proof the Rust
  verifier accepts, the calldata, the EVM result, the trapdoor, and mutants, so that the
  acceptance gate of the widened class is a computation.
- **Needs.** WID.3's exporter; REF.11's `MIDFALL_CONFORMANCE_SRS=unsafe:<seed>` mode;
  `proofs/src/poly/kzg/params.rs` (`unsafe_setup`, `downsize`);
  `ivc_keccak_solidity.rs` (`load_srs`, `SrsSource`, the leaf-bundle mode).
- **Does NOT need.** The Lean side.
- **Do.**
  1. Add a test-SRS source: ONE `ParamsKZG::unsafe_setup(20, seeded rng)`, and the k = 19 SRS as
     its `downsize(19)`. Assert `ivc_srs.s_g2() == decider_srs.s_g2()` (clause 8; add the same
     assertion to the production path of the e2e test).
  2. Run the full flow (two IVC leaves, the decider proof, the EVM call) and export schema 2:
     `proof.bin`, `calldata.bin`, `instances.json`, `evm.json`, `trace.json` including the two
     collapsed accumulator points and `alpha` and the 0x0f call input, `params.json` with the
     trapdoor.
  3. `mutations.json`: REF.11's corpus, plus four accumulator mutants (a limb moved across a word
     boundary; a coordinate ≥ the field modulus; the identity flag set with non-zero coordinates;
     a scalar ≥ r) and one proof whose inner opening is bad while the outer proof verifies. Each
     with the Rust verdict and the EVM result.
- **Deliverable.** The bundle, its manifest, the exporter mode.
- **Accept.** `trace.json`: verdict accept, EVM returns `true`; every mutant is rejected by the
  EVM; the manifest verifies.
- **Stop if.** The two SRS cannot share a trapdoor without a change under `proofs/src`: report the
  API that is missing.
- **Guidance.** Two different trapdoors would make the batched pairing fail for every proof: the
  contract pairs both the KZG check and the accumulator against one `[s]₂`.

### WID.5 — `generateAll` in accumulator and external-evaluator mode; three artifact gates

GEN · PORT · box 2.5 h · strongest · after OBJ.7, WID.3

- **Goal.** `generateAll` (OBJ.7) returns, for the exported decider key and options, the three
  files of WID.3 byte for byte, with the evaluator's runtime length and code hash taken as inputs.
- **Needs.** OBJ.7's `generateAll`; `Generator/Builder.lean` (`externalQuotient` :252,
  `renderQuotientEvaluator` :355), `Generator/Contracts.lean:490`
  (`renderHalo2QuotientEvaluator`), `Generator/LoweringPlan.lean:328`
  (`quotientExternalFrame`), `Generator/Artifacts.lean:270-347` (accumulator expectations);
  `design/ivc-object-reference.md` §A.
- **Does NOT need.** Any Yul semantics; the proof bytes.
- **Do.**
  1. Extend the glue so the accumulator encoding and the external-quotient option reach the plan.
  2. Take `expectedQuotientLength` and `expectedQuotientCodehash` from `build.json` (they are solc
     output and can only be inputs); state this in the module header.
  3. Three `ArtifactEq`-style KATs against the bundle's `.sol` files.
  4. Sub-KATs, each a card-sized child if it fails: the quotient program build on the decider
     constraint system (opcode `0x21 MODARITH7`, 143 program words, 178 constants) and the PCS
     emitter (5 point sets, a 78-pair MSM).
- **Deliverable.** The glue and the three gates.
- **Accept.** Three KATs `true`; one mutant per file (a flipped byte of the bundle) makes its KAT
  `false`.
- **Stop if.** A file differs outside `BUILD_ID`: report the first differing region and which
  emitter owns it; one child card per emitter.
- **Guidance.** Seven partials already match (WID.2). The untested parts are the quotient plan on
  real limb shapes and the evaluator shell.

### GEN.2 — Clause table of the widened class on both test keys  **[rewritten by PL.G]**

INFRA · KAT · box 1.5 h · Sonnet · after WID.3, WID.1

- **Goal.** A table, printed by Lean, of every decidable clause of `SupportedV3` and `SupportedW`
  on the F1 key and on the IVC decider key.
- **Needs.** WID.3's bundle; `SupportedV3` (`StatementsV3.lean:592`), `SupportedW`
  (`WideningV3.lean:101`), `AccShape` :83, `ExternalPinned` :93.
- **Does NOT need.** Any proof; the proof bytes.
- **Do.**
  1. `#eval` each clause on both keys and print the counts behind them (phases, challenges,
     instance columns, lookups, trashcans, point sets, `k`, accumulator kind, tail length).
  2. Expected on the IVC key (read off the artifact, `design/ivc-object-reference.md` §A5):
     `noAcc` and `embeddedQuotient` false; every other `SupportedV3` clause true; every
     `SupportedW` clause true. Expected on F1: everything true.
- **Deliverable.** The KAT file and the table in the report.
- **Accept.** The table is produced by `#eval`; it matches the expectation, or the report names
  each clause that differs.
- **Stop if.** A `SupportedW` clause is false on the IVC key: the class does not cover the IVC
  verifier; report the clause and the measured value, and ask the human.

### WID.6 — The evaluator as an object: `evalBodyOf` and its scans

> **Tree, not parse.** A parsed stand-in is unfit for a proof by induction over the emitter (OBJ.2's own guidance), and OBJ.15 excludes the external arm. Step 1 is therefore: extend OBJ.15's interpreter-template emitter to the external arm and emit the evaluator's wrapper as a tree (`evalBodyOf`); the parse of the rendered text is used only for the token-agreement KAT against `renderHalo2QuotientEvaluator`.


GEN · STATEMENT · box 2.5 h · strongest · after WID.5, OBJ.2

- **Goal.** `EvalObject` becomes a function of the render: the evaluator's Yul body as an AST, tied
  to the rendered text, with the two decidable scans the rows need.
- **Needs.** `EvalObject` (`WideningV3.lean:314`), `EvalPins` :785, `ValidW` :800; OBJ.2's token
  parser and its `codegenStruct` pattern; `Generator/Contracts.lean:490`.
- **Do.**
  1. `evalBodyOf : PlanView → Model → YulBlock` by parsing the rendered fallback body (the OBJ.2
     route), and `evalObjectOf R : EvalObject`.
  2. Add to `ValidW` (not frozen yet) the clause `Q = evalObjectOf R` and the scans: the evaluator
     body contains no call, no `gas()`, no environment read other than calldata; in the verifier,
     `gas()` occurs only as the gas argument of a call.
  3. Witness: both scans `true` at the WID.3 bundle. Falsifier: a body with one `gas()` inserted
     fails the scan; a body with one token changed fails the token-agreement clause.
- **Deliverable.** The definitions, the clause, witness and falsifier (W12).
- **Accept.** The three `#eval` results as stated; `verify.sh --quick` green.
- **Stop if.** The parser does not cover a construct of the evaluator text: report the construct
  (a child card for the parser, as OBJ.2 handles it).

### RECON.3 — Move the row families to the widened shape (D-P72 clause 1)

> **Critic's finding, applied.** The reduction of step 2 transports a row only at a render with no accumulator and an embedded evaluator. A row is needed at accumulator and external renders too (WID.14 assumes it). So step 3 is: restate **every** row under `ValidW R Q` (`ValidCore R ∧ SupportedW R`). The table at the top of `lean/widening/WideningStages.lean` says which rows use `noAcc` or `embeddedQuotient`: the others carry over verbatim; those that do (prefix, vkLoading, quotientLin, finalPairing, totality) keep their base arm and get their second arm in WID.13, WID.15, WID.16, WID.19 and a prefix child. The one-arm rows (transcriptParser, lagrange, pcs, traceReturn) are still restated over `StageInvW`, each with two frame obligations: the accumulator slots are not written and `quotientEvaluator` is not assigned. **`StageInv` of V3 is unsatisfiable after `.start` in accumulator mode** (`stageInv_false_of_acc`: `Inv`'s `.vk` clause, `Lowering/Inv.lean:754`, needs a snapshot with an accumulator and every staged snapshot has none); `StageInvW` reads the accumulator-carrying snapshot and equals `StageInv` at V3's corner (`stageInvW_iff_V3`, proved). Because of this, GEN.1, T3.9 and SIM.6 are also `after RECON.3`: each row is proved once, in the widened shape. Progress rows are stated for every functional gas oracle (`CompleteAnyGasW`, D-P72 clause 5); the headline's zero-oracle conjunct follows by `CompleteAnyGasW.toComplete`.


SEM · STATEMENT · box 2.5 h · strongest · after RECON.2, WID.1

- **Goal.** `SimContracts`, `ProgContracts` and the composition are stated once, in the widened
  shape, before any ROW card of M6 is briefed, so that the base-class rows need no restatement
  when the two new arms are proved.
- **Needs.** `WideningStages.lean`: `StageInvW` S :317, `BlockSimW` S :555, `SimContractsW` S :569,
  `BlockProgSW` S :588, `ProgContractsW` S :601, `leanStageW_noAcc` S :179; `WideningV3.lean`:
  `lowering_equivalenceW_of` :604, `equivalenceW_iff_V3` :637; RECON.2's composition.
- **Do.**
  1. State `lowering_equivalence_of_stagesW`: the widened headline from `SimContractsW`,
     `ProgContractsW`, `TotalW`, `EvalContracts` and the scans. Prove it by replaying RECON.2's
     composition with `StageInvW`.
  2. Prove the reduction: at a render with no accumulator and an embedded evaluator,
     `BlockSimW R q … ↔ BlockSim R q …` (from `leanStageW_noAcc` and `callsW_embedded`).
  3. Re-point the generic row statements of `GeneratorRows.lean` at the `W` families; the rows
     already proved (`.traceReturn`, `.vkLoading` if merged) are transported by step 2.
- **Deliverable.** The composition, the reduction, the re-pointed statements.
- **Accept.** `#assert_axioms` on the composition and the reduction: standard three, empty native
  list. Witness: the reduction instantiated at `poseidonRender`. Falsifier: `acc_not_supportedV3`
  (`WideningV3.lean:123`) shows the V3 families do not cover an accumulator render.
- **Stop if.** The reduction is false for a clause of `StageInvW`: report the clause.

### WID.11 — The two ALG obligations and the limb lemma

ALG · PROOF · box 2.5 h · strongest · after WID.1

- **Goal.** `instWords_of_decoded` (`WideningStages.lean:134`), `batchedCheck_iff_contract` (:292)
  and a new, stated lemma that the contract's `(hi, lo)` reconstruction of a 7×56-bit coordinate
  equals the port's sum-and-split.
- **Needs.** `Lowering/Accumulator.lean`: `batchedCheck_eq` :1194, `dualMsm_check_iff_contract`
  :1320 (both proved); `Halo2/Exec/Accumulator.lean:362-370` (the port); the contract's
  `load_acc_coord_shifted` (IVC `Halo2Verifier.sol:980-1011`).
- **Do.**
  1. STATEMENT first (W12): the limb lemma as an equation between two `Nat` functions of seven
     limbs below `2^56`, with `decoder_accepts` (`WideningTests.lean:73`) as witness and a limb
     moved across the 256-bit boundary as falsifier.
  2. Prove it by `omega`-style arithmetic on the split at bit 256 (limb 4 straddles).
  3. `batchedCheck_iff_contract` from the two v1 lemmas; `instWords_of_decoded` from
     `decodeCalldata`'s instance clause.
- **Deliverable.** Three theorems, sorry-free.
- **Accept.** `#assert_axioms` each: standard three, empty native list.
- **Stop if.** `batchedCheck_iff_contract` needs a base-point pin `PayloadAgrees` does not have:
  PREMISE GAP with the goal.

### WID.12 — Call summaries for the six accumulator helpers

SEM · PROOF · box 2.5 h · strongest · after HLP.1, WID.11, OBJ.2, OBJ.13

- **Goal.** One call summary with its `CSound` proof for each of `load_acc_coord_shifted`,
  `is_bls_p_minus_one`, `check_acc_coord_packing`, `load_acc_coord`, `load_acc_point`,
  `validate_public_accumulator`, in HLP.1's generic form ("the scope of a valid render defines
  helper f with this body").
- **Needs.** HLP.1's pattern and its two summaries; the helper ASTs (OBJ.2; they are the 823
  tokens PLAN-V3 §3 lists as missing from the AST); WID.11's limb lemma.
- **Do.** One summary per helper, bottom-up in the order listed. The two loops have LITERAL
  bounds at their only call sites (7 limbs, 2 coordinate words): unroll them with GEN.0's
  parametric execution; the loop rule is not needed. `validate_public_accumulator` makes two
  `staticcall`s to `0x0c`: use `Holds.g1Msm1`.
- **Deliverable.** Six summaries.
- **Accept.** `#assert_axioms` each: standard three, empty native list; each summary is used by
  the one above it.
- **Stop if.** A helper's body differs between two valid renders other than through layout
  constants: report the difference (the summary must then take it as a parameter).

### WID.13 — vkLoading row, accumulator arm: establish `AccInv`

SEM · SKELETON · box 2.5 h · strongest · after GEN.1, RECON.3, WID.12

- **Goal.** `BlockSimW R .vkLoading` and its progress row at a render with an accumulator: on a
  normal exit with `success = 1`, `AccInv` (`WideningStages.lean:150`) holds; otherwise the block
  reverts.
- **Needs.** GEN.1's row (the no-accumulator arm) and its proof pattern; WID.12's summary of
  `validate_public_accumulator`; `Holds.g1Decodes`, clause 6's `idLaw`.
- **Do.** State the two halves and the requirements table; issue PROOF children in GEN.1's
  pattern: the header guards with `HAS_ACCUMULATOR = 1`, the validation call, the `AccInv`
  clause. Progress premise: `AccDecodes R cd` (`accDecodes_of_leanAcceptsAcc`, S :373).
- **Accept.** The skeleton compiles with its children as named sorries; witness and falsifier for
  each child (W12): the F2 calldata and WID.4's four accumulator mutants.
- **Stop if.** `AccInv` needs the proof to decode (it must not: it is stated on raw instance
  words).

### WID.14 — Frame clauses: three rows do not write the accumulator slots

> **Routed `strongest` after review.** The "write-set lemma" of each row does not exist yet: each of ROW.TP, T3.9 and ROW.PCS must deliver one (a statement that the block writes only inside named windows). This card states the three, proves the frame clause from each, and is not READY until those rows are merged.


SEM · PROOF · box 2 h · strongest · after ROW.TP, T3.9, ROW.PCS, RECON.3

- **Goal.** The transcriptParser, lagrange and pcs rows preserve `AccInv`: their write sets miss
  `[accLhsMptr, +128)` and `[accRhsMptr, +128)`.
- **Needs.** The three merged rows and their write-set lemmas; `ValidW`'s layout clause.
- **Do.** One lemma per row: from the row's recorded write set and layout disjointness, memory at
  the two slots is unchanged; conclude `AccInv` at the exit from `AccInv` at the entry.
- **Accept.** `#assert_axioms` each: standard three, empty native list.
- **Stop if.** A row's write set is not disjoint from the slots for some valid layout: that is a
  finding about the generator's memory plan; report the layout.

### WID.15 — finalPairing row, batching arm: `BatchedInv`

SEM · SKELETON · box 2.5 h · strongest · after ROW.FP, RECON.3, WID.11

- **Goal.** `BlockSimW R .finalPairing` at a render with an accumulator: after the batching block
  the two pairing slots hold the reference's batched inputs (`BatchedInv`, S :277), and the
  `ec_pairing` result is `accFinalCheck`.
- **Needs.** ROW.FP's row and pattern; `batchedCheck_iff_contract`; the block
  (IVC `Halo2Verifier.sol:2516-2562`: one `keccak256` over `0x240` bytes, two G1MSM, two G1ADD);
  `alphaOf` (`Lowering/Accumulator.lean`, argument order: see its doc comment — the hashed
  preimage order is tag, vk digest, RHS, LHS, ACC_RHS, ACC_LHS).
- **Do.** State the halves; children: the preimage layout equals `alphaOf`'s; `mod(keccak, r)`
  with the zero-to-one arm equals `frOfDigest`; the two MSMs and adds; the poisoned arm
  (`if success { … }`).
- **Accept.** Skeleton with named children; W12 per child (F2 trace `alpha`; a swapped preimage
  order as falsifier).
- **Stop if.** The emitted preimage order differs from `alphaOf`'s: a divergence between the
  contract and the reference; report both orders and ask the human.

### WID.16 — quotientLin row, external arm

SEM · SKELETON · box 2.5 h · strongest · after ROW.Q, RECON.3, WID.6

- **Goal.** `BlockSimW R .quotientLin` at an external render: pre `StageInvW .lagrange`, post
  `StageInvW .quotient`, consuming `EvaluatorTrust` and `EvalContracts`.
- **Needs.** The slice (IVC `Halo2Verifier.sol:1803-1829`): the pin guard, `gas()`, the
  `staticcall`, two checks, one `mstore`, a copy loop over the simple selectors; `QPinned` :374,
  `EvaluatorTrust.spec`, `evalRel_answers` S :496; the loop rule (GEN.3) for the copy loop
  (bound = number of simple selectors).
- **Do.** State the halves; children: guard ⇒ `QPinned` or revert; a successful answer is a run
  of the body (`EvaluatorTrust.spec`); the returned words (`EvalBodyShape`, `EvalBodyAgree`); the
  copy loop; the failure paths (call fails, wrong return size, wrong magic) each revert.
- **Accept.** Skeleton with named children; W12 per child.
- **Stop if.** Conjunct 3 (two outcomes) needs a fact about the evaluator: it must not (a
  `staticcall` cannot change the world; `TwoOutcomesW` is proved from the scans).

### WID.17 — The evaluator body: shape, agreement, totality

SEM · SKELETON · box 2.5 h · strongest · after ROW.Q, WID.6

- **Goal.** `EvalContracts R Q` (S :251) for every valid external render: `EvalBodyShape`,
  `EvalBodyAgree`, `EvalBodyTotal`.
- **Needs.** ROW.Q's route-B proof (the interpreter loop refines the reference VM), **stated over
  a memory window and a dialect parameter** so it serves both the verifier's slice and the
  evaluator's body; `Generator/Artifacts.lean:428` (`validateLayout`: the frame contains
  everything the numerator reads); the wrapper (length test, `calldatacopy`, the magic word, the
  bucket copy, `return`).
- **Do.** Children: (1) the dialect bridge — a block with no call and no `gas()` runs the same in
  `EVM.evm` and in `Bridge.Dialect` with no externals; (2) the transport lemma — callee memory
  after `calldatacopy` equals the caller's window, scratch outside is zero; (3) the wrapper;
  (4) the numerator through ROW.Q's theorem at the transported window; (5) the opcode
  `0x21 MODARITH7` arm of the interpreter refinement; (6) totality on EVERY input, including
  frames no valid run produces.
- **Accept.** Skeleton with named children; W12: the run-it gate with the slot answered by the
  interpreter; an input one byte short reverts; a program byte flipped to an unused opcode
  reverts.
- **Stop if.** ROW.Q was proved for the verifier's slice only (no window parameter): stop; ROW.Q
  is restated first.
- **Guidance.** The evaluator's real entry memory is not all-zero (solc's prologue writes the
  free-memory pointer): `EvalEntry` says what is assumed; clause 9 asks for a guard.

### WID.19 — Totality, widened

SEM · PROOF · box 2.5 h · strongest · after TOT.1, WID.16, WID.17

- **Goal.** `TotalW R Q product` (`WideningV3.lean:572`) for every valid render.
- **Needs.** TOT.1's generic proof; `EvalBodyTotal`; the scan "`gas()` only as the gas argument of
  a call" (WID.6), which replaces TOT.1's "no `gas()`" premise.
- **Do.** Replay TOT.1 with `callsW`; at the evaluator call use `EvalBodyTotal` and
  `evaluatorTrust_le_permissive` (:402).
- **Accept.** `#assert_axioms`: standard three, empty native list.
- **Stop if.** Totality needs the evaluator to be total only on frames a valid run produces: it
  must be total on every input (WID.17 child 6); if that child is open, this card is not READY.

### WID.H — The widened headline and the definition of done

INFRA · PROOF · box 1.5 h · strongest · after PL.H, RECON.3, WID.13–WID.19, WID.9

- **Goal.** `lowering_correctW` sorry-free; `lowering_correct` as its corollary; `GeneratorDone`
  with a second non-vacuity field at F2.
- **Needs.** `WideningV3.lean`: `lowering_equivalenceW_of` :604, `lowering_correctW` S :652,
  `lowering_correct_of_W` S :698, `model_quotientMode` :808, `HypothesesInhabitedW` :704;
  RECON.3's `lowering_equivalence_of_stagesW`; the rows WID.13–WID.17 and WID.19; WID.9's gate;
  DG.4's `Done`.
- **Do.** `lowering_equivalence_of_stagesW` applied to the rows; `model_quotientMode` (a fact
  about `generateVerifierFromPlan`, by cases on the flag); add to `GeneratorDone`
  `nonvacuousAcc : ValidW ivcRender Q ∧ ∃ product, HypothesesInhabitedW ivcRender Q product` and
  the three artifact fields for F2.
- **Accept.** `#assert_axioms lowering_correctW [propext, Classical.choice, Quot.sound]` with an
  empty native list; the report prints `0 sorried leaves`.
- **Stop if.** A proof is needed here beyond composition: a leaf was mis-stated; report it.

### WID.7 — `ivcRender` and its validity by computation (test)

GEN · KAT · box 2.5 h · strongest · after WID.5, WID.6, WID.4, OBJ.9

- **Goal.** The render of test fixture F2 as a Lean term, and `ValidW ivcRender (evalObjectOf
  ivcRender)` decided clause by clause — the F2 analogue of OBJ.8/OBJ.9. It is a test (the
  non-vacuity witness of the widened class), not a row.
- **Needs.** WID.5's `generateAll` on the decider key; WID.6's `evalObjectOf`; WID.4's bundle;
  OBJ.9's clause table for F1 (the pattern); `ValidW` :800, `EvalPins` :785, `SupportedW` :104.
- **Do.** Build `ivcRender` from the bundle as OBJ.9 builds `poseidonRender`; `#eval` every
  decidable clause of `ValidW`; one mutated render per clause as falsifier.
- **Deliverable.** `Midfall/Instances/IvcRender.lean`; the clause table.
- **Accept.** Every decidable clause `true`; every mutant `false` on its clause. `native_decide`
  is allowed here (a fixture file) and nowhere in a row.
- **Stop if.** A clause is `false` at F2: the widened class does not contain the IVC verifier;
  report the clause and ask the human.

### WID.8 — Reference gate at F2: the accumulator, `alpha` and the two pairing inputs

ALG · KAT · box 2.5 h · Sonnet · after REF.10, WID.4, WID.1, WID.7

- **Goal.** The Lean reference, run on the F2 proof, reproduces Rust's two collapsed accumulator
  points, `alpha`, and the two inputs of the final pairing (`PairingInputsAgree`,
  `WideningV3.lean:734`).
- **Needs.** REF.10's staged run (`lean/reference/RunLib.lean` pattern); WID.4's `trace.json`;
  `decodeAcc`, `alphaOf`, `batchedInputs` :726.
- **Do.** Stage the run as REF.10 does (decode, transcript, MSM), then decode the accumulator from
  the raw instance words, collapse, derive `alpha`, form the batched inputs; compare each with
  the trace. Mutants: WID.4's four accumulator mutants are refused at decode.
- **Accept.** Every comparison `true`; every mutant `false` at the intended stage; total run
  under 60 s (F1's staged run: 8.9 s measured).
- **Stop if.** A comparison fails: a divergence between the Lean reference and Rust; report the
  first differing value and ask the human (goal prompt: ASK THE HUMAN).
- **Guidance.** First real-proof exercise of: two lookups, six permutation sets, rotation −1, five
  point sets, 16 instances, k = 20.

### WID.9 — Acceptance gate at F2 (test SRS)

ALG · KAT · box 2 h · Sonnet · after WID.8, REF.12, WID.5, WID.7

- **Goal.** `HypothesesInhabitedW ivcRender Q product` at the F2 calldata: `LeanAcceptsAcc` holds
  by computation with the constructed pairing at the known trapdoor.
- **Needs.** REF.12's acceptance gate (the F1 pattern); `pairingC`; WID.4's trapdoor.
- **Do.** As REF.12, with `accFinalCheck` in place of `DualMSM.check`. Check `AccNontrivial`
  (:690): the accumulator is not the identity pair, so the batched arm is exercised.
- **Accept.** The gate is `true`; the bad-inner-opening mutant of WID.4 is `false` at the final
  check and nowhere earlier.
- **Stop if.** The mutant is rejected before the pairing: the test does not exercise the batched
  check; report where.

## Area CERT — the generator is certified  **[D-P73, signed 2026-11-17]**

Milestone M10 of PLAN-V3 §5. The final theorem has hypotheses on the generator's **input** only:
`generator_correct (gi) (o) (hg : Generates gi o) (hs : SupportedInput gi) (product)`. Evidence,
typechecked by `bash docs/plans/V3-evidence/check.sh object`:
`lean/object/GeneratorCertified.lean` (33 named open lemmas; `generate_spec`,
`generator_certified`, `generator_correct`, `generator_correct_V3` proved from them),
`CertMeasure.lean` (each lemma's decidable conclusion evaluated at F1: all `true` except the two
codegen clauses), memo `design/generator-certified.md`.

- **Every lemma named in a card is a declaration of `GeneratorCertified.lean`; find it by name.**
  Each has the shape `(hg : Generates gi o) (hs : SupportedInput gi) : <one clause of ValidV3 at
  renderOf gi o>`.
- **Routing.** A family's first lemma is `strongest`; the Sonnet-only split is one lemma per
  child, each with the family's evidence file and stop conditions.
- **A lemma that is false for some supported input is a finding for the human** (D-P73 clause 3):
  land the counterexample input, do not add a hypothesis to `SupportedInput`.
- Every Accept line means `#assert_axioms <name> [propext, Classical.choice, Quot.sound] native []`.

### CERT.0 — Land the certified statement (no frozen edit)

GEN · PORT · box 2 h · Sonnet · after OBJ.7, ST.1

- **Goal.** `GenInput`, `generate`, `Generates`, `renderOf`, `SupportedInput`, the 33 lemma
  statements, `generate_spec`, `generator_certified`, `generator_correct` and
  `generator_correct_V3` compile in the tree, with the 33 open lemmas registered.
- **Needs.** `docs/plans/V3-evidence/lean/object/GeneratorCertified.lean` (510 lines),
  `CertMeasure.lean`; OBJ.7's `generateAll` and `GeneratedBy`; ST.1's module (for `ValidV3` and
  `lowering_correct`); `Midfall/Generator/Vk.lean` (`generateVk`; the instance `[DecidableEq G₂]`
  it needs, `:300`).
- **Does NOT need.** A proof of any lemma; any Yul semantics.
- **VERIFY FIRST.** `check.sh object`: `GeneratorCertified` prints `ok` with 33 sorry warnings and
  `CertMeasure` prints `ok`.
- **Do.**
  1. Port the file verbatim to `Midfall/Generator/Certified.lean` (statements) and
     `Midfall/Instances/CertMeasure.lean` (the F1 evaluation); change only imports.
  2. Register the 33 sorries by name, grouped by the card that owns each (PLAN-V3 §5 M10 table).
  3. `#print axioms generate_spec` (expected: no `sorryAx`).
- **Deliverable.** The two modules; the register rows.
- **Accept.** `lake build` green; `CertMeasure` prints `true` for every decidable conclusion
  except `prog_codegenStruct` and `v3_codegen` (they are `false` until CERT.2); `Frozen.sha256`
  unchanged.
- **Stop if.** `generate`'s three steps do not typecheck against the landed `generateAll`: report
  the first error; do not restate `generate`.

### CERT.1 — Probe the two suspects: `v3_planMeta` and `v3_cdBound`

GEN · PROBE · box 2.5 h · strongest · after CERT.0

- **Goal.** For each of the two lemmas: a proof sketch that closes, or a supported input for
  which it is false.
- **Needs.** `GeneratorCertified.lean`: `v3_planMeta`, `v3_cdBound`; `PlanMeta`
  (`StatementsV3.lean`), `ValidV3.cdBound` (:645); `Generator/LoweringPlan.lean` (`newFromVk`,
  where `Data.new` is called and with which memory layout); the Rust it ports
  (`proofs/solidity-verifier/src/lowering/vk.rs:504-519`); `design/generator-certified.md` §2.
- **Do.**
  1. `v3_planMeta`: compare, step by step, the memory layout `Data.new` receives in the port with
     the one Rust passes. If they differ for some input, build that input (a constraint system
     with one more lookup or column than F1) and `#eval` both sides.
  2. `v3_cdBound`: `proofEnd + 32 + 32·numInstances < 2^256`. Find what bounds `proofEnd` in terms
     of the key (number of commitments and evaluations) and whether `sizeBound` (`k < 64`,
     `numInstances < 2^64`) implies it; if not, state the smallest additional input bound that
     does, as a candidate clause.
- **Deliverable.** For each lemma: PROVABLE (with the sketch) or FALSE (with the input landed as a
  KAT) or NEEDS CLAUSE (with the candidate clause, typechecked).
- **Accept.** The report's three-way verdict for both, each backed by a compiled file.
- **Stop if.** A lemma is FALSE or NEEDS CLAUSE: stop and ask the human (D-P73 clause 3). The
  orchestrator does not edit `SupportedInput`.

### CERT.2 — Route A: the generator prints the tree

GEN · PORT · box 2.5 h · strongest · after OBJ.13, OBJ.14, OBJ.15, ROW.Q, OBJ.7, CERT.0

- **Goal.** The Lean generator's two assembly blocks are `EVM.print` of the emitted tree; the
  template-text port stays as a test oracle; `prog_codegenStruct` and `v3_codegen` hold by
  construction.
- **Needs.** A complete tree emitter: `mainAsmRaw pv` must print to the same tokens as the port's
  main block (today 6,761 against 14,054 tokens at F1: the accumulator helpers, the quotient
  helpers and the numerator block are missing — OBJ.13, OBJ.14, OBJ.15 and ROW.Q's emitter
  children); `Program.lean:190` (`codegenAgrees`), `ObjectV3Full.lean:728` (`codegenStruct`);
  `Generator/Builder.lean` (where the assembly text enters the rendered file);
  `design/generator-certified.md` §3 (the measurement and the solc options).
- **VERIFY FIRST.** `codegenAgrees pv m = true` at F1 (the tree is complete). If it is `false`,
  this card is NOT READY: report the first differing token and which emitter owns it.
- **Do.**
  1. Define the certified render of `Halo2Verifier.sol`: the port's text with both assembly
     blocks replaced by `EVM.print` of `abiGuardBlock m` and `mainAsmRaw pv`.
  2. Artifact gate, route-A form: outside the assembly blocks byte equality with the Rust
     artifact; inside, token equality (`yulTokens`). Keep the byte-equality gate of the template
     port as the oracle's own test.
  3. Repeat the bytecode measurement with the **pinned** solc binary (0.8.30, the project's
     options: `--via-ir --optimize --evm-version cancun --no-cbor-metadata`): the template text
     and the printed-tree text compile to identical runtime and creation bytecode at F1 and F2.
     Record the binary's sha256.
  4. Prove `prog_codegenStruct` and `v3_codegen` for the certified render (they reduce to a
     print-then-parse fact on the emitted tree; if that needs a general round-trip theorem, state
     it and stop: it is item X12).
- **Deliverable.** The certified render; the two gates; the bytecode KAT; the two lemmas or the
  stated round-trip obligation.
- **Accept.** Both gates `true` at F1 (and F2 when its bundle exists); bytecode identical with
  the pinned binary; `CertMeasure` prints `true` for the two codegen clauses.
- **Stop if.** The bytecode differs with the pinned binary: stop and ask the human; route A's
  premise is false.

### CERT.3 — `Constants.sol` is printed from the constant table

GEN · PORT · box 2 h · Sonnet · after CERT.0

- **Goal.** The constants file is rendered from `expectedConsts pv m` (data first), so that
  `prog_constLinesLiteral` and `prog_constTable` hold by construction instead of by reading
  strings back.
- **Needs.** `ObjectV3Full.lean`: `expectedConsts`, `constTableOf`, `constLinesLiteral`;
  `Generator/Contracts.lean` (`renderConstants`).
- **Do.** Define the constants text as the print of the table; KAT: byte-equal to the port's
  `renderConstants` output at F1; prove the two lemmas by unfolding.
- **Accept.** The KAT is `true`; a mutated table entry makes it `false`; the two lemmas pass
  `#assert_axioms` with an empty native list.
- **Stop if.** The port prints a constant the table does not hold (or the reverse): report the
  name; that is a coherence defect, not a formatting one.

### CERT.4 — Family (a): what the generator's own validation checks

GEN · PROOF · box 2.5 h · strongest · after CERT.0

- **Goal.** `prog_transcriptFloor`, `supported_layout`, `v3_invariants`, `env_nG2`.
- **Needs.** `generate_spec` (proved: the chain of successful steps);
  `Generator/LoweringPlan.lean:534-538` (`validateGeneratorInvariants`), `Generator/Layout.lean`
  (`memory.validate` :1023, `MemoryMap.validate` :552), `Generator/Vk.lean:806` (the G2 count
  check, `vk.rs:180`).
- **Do.** For each lemma: from `generate_spec` obtain the step that ran the check; unfold the
  check; read the clause off its success branch. First `v3_invariants` (it is the check itself),
  then the two layout lemmas, then `env_nG2`.
- **Accept.** Four lemmas sorry-free; witness: `CertMeasure` at F1; falsifier per lemma: an input
  the generator rejects at that check (a KAT that `generate` returns the corresponding error).
- **Stop if.** A clause is not implied by the check that was supposed to give it: report the gap
  between the check and the clause.
- **Guidance.** Sonnet-only split: one lemma per child, `v3_invariants` first.

### CERT.5 — Family (b): syntactic invariants of the tree emitters

GEN · SKELETON · box 2.5 h · strongest · after CERT.0, GEN.4, the tree emitter complete (as CERT.2)

- **Goal.** `prog_constsDeclared`, `prog_callsResolved`, `prog_noWriters`, `v3_exitDiscipline`
  (one child each), and `prog_noShadow`, `prog_closed`, `v3_closed`, `v3_noShadow`.
- **Needs.** The scans: `NoWriters`, `ExitDiscipline` (`StatementsV3.lean:520-526`),
  `callsResolved`, `noShadow`, `freeNames` (`ObjectV3Full.lean`); the emitters of
  `Lowering/GenAst*.lean`; GEN.4 (the inliner over a concatenation); `helpers_eq`
  (`GeneratorRows.lean`).
- **Do.**
  1. For each scan state one lemma per emitter group ("the output of `emitX` satisfies the scan,
     for every plan view") and one composition lemma over `mainAsmRaw`.
  2. Prove the scan for the fixed-text groups by `kernel_rfl`-style normal forms; for the
     list-mapped groups by induction over the list.
  3. Issue the four children with their per-group lemma lists.
- **Accept.** The skeleton compiles with named children; W12 per scan: the F1 evaluation as
  witness; a tree with one `sstore` (resp. one early `return`, one unresolved call, one shadowed
  constant) inserted as falsifier.
- **Stop if.** An emitter's output violates a scan for some plan view: that is a defect of the
  generator; land the plan view and ask the human.

### CERT.6 — Family (c): builder lemmas

GEN · PROOF · box 2.5 h · strongest · after CERT.0, CERT.3

- **Goal.** `plan_vk_of_generateAll`, `prog_noDirect`, `prog_constNodup`, `env_k`,
  `env_negLagranges`, `v3_layout`, `v3_model`, `v3_pins_of_valid`; and `payload_header`.
- **Needs.** `generate_spec`; `renderOf`; `Generator/LoweringPlan.lean` (`newFromVk`),
  `Generator/Vk.lean` (`VkHeaderBuilder`; the reservation fold rewrites only the quotient
  sections), `EnvAgrees` (`Lowering/Inv.lean:533-590`).
- **Do.** Each lemma unfolds one builder: the eight small ones first (one child each for a
  Sonnet-only run), then `payload_header` (its own child: the header words are the key's fields;
  `sizeBound` is what makes the `Nat`-to-word conversion exact).
- **Accept.** Nine lemmas sorry-free; W12: `CertMeasure` as witness; for `payload_header` a
  falsifier with `numInstances = 2^64` (the header word wraps: this is why `sizeBound` exists).
- **Stop if.** `payload_header` needs a bound `sizeBound` does not give: report it (a candidate
  clause for the human).

### CERT.7 — Family (c)+(d): the payload and the key, through the codec laws

GEN · PROOF · box 2.5 h · strongest · after CERT.6, REF.5

- **Goal.** `env_vkDigest`, `payload_g1Base`, `payload_g2Base`, `payload_negSG2`, `payload_comms`,
  `v3_payload`.
- **Needs.** `SupportedInput.g1Codec`, `g2Codec` (the two codec laws); `PayloadAgrees`
  (`StatementsV3.lean`); `Generator/Encoding.lean` (`g1ToU256s`, `g2ToU256s`); the checks at
  `vk.rs:151` and `:180`; REF.5's codec instance (the witness that the two laws hold for the
  computable codec).
- **Do.** One lemma per payload region: the words the generator writes are `toEip` (resp.
  `encG2`) of the key's point, by the codec law; `payload_negSG2` uses the SRS point as data
  (D-P62). `v3_payload` is their conjunction.
- **Accept.** Six lemmas sorry-free; W12: the two codec laws hold at the computable codec
  (witness); a codec with one byte swapped fails `payload_comms` (falsifier).
- **Stop if.** A payload region is written from something other than the key or the SRS.

### CERT.8 — `generate` runs on a real key

GEN · PORT · box 2.5 h · strongest · after CERT.0, REF.5g

- **Goal.** `generate gi` evaluates to `.ok o` on the F1 key (and on the F2 key when its bundle
  exists), so that "produced by the Lean generator" is something that can happen.
- **Needs.** What blocks it today: `generateVk` needs G2 points from the SRS and there is no
  computable G2 decompression (`design/generator-certified.md` §4); REF.5g (the G2 side of the
  curve model); `GenInput.codecs`.
- **Do.** Supply `GenInput` at F1 from the bundle with the G2 points given in uncompressed form
  (the exporter writes them, REF.11 schema 2), so that no decompression is needed; `#eval`
  `generate`; compare `renderOf` with `poseidonRender` field by field.
- **Accept.** `generate` returns `.ok`; the rendered files pass the route-A artifact gates; the
  run takes under 60 s.
- **Stop if.** The generator needs a compressed G2 input that cannot be avoided: report the call
  site.

### CERT.H — `generator_correct`, and the definition of done

INFRA · PROOF · box 1.5 h · strongest · after CERT.1–CERT.8, PL.H, WID.H

- **Goal.** `generator_certified` and `generator_correct` sorry-free (and their `W` forms after
  M9); `Done`'s headline is `generator_correct`.
- **Needs.** `GeneratorCertified.lean` §6–§7 (the two theorems are already proved from the 33
  lemmas); `lowering_correct` / `lowering_correctW`; DG.4's `Done`.
- **Do.** Nothing is proved here. Replace `Done.proof.headline` by the input-only form and
  `nonvacuous` by "`generate` succeeds on the test key and the gate holds at its render"; add the
  axiom gate; rewrite the English statement's first item (PLAN-V3 §6).
- **Accept.** `#assert_axioms generator_correct [propext, Classical.choice, Quot.sound] native []`;
  `#cone_report generator_correct: 0 sorried leaves`.
- **Stop if.** A proof is needed beyond composition: a lemma was mis-stated; report it.
