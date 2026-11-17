<!-- Design memo behind PLAN-V3 (M1 — the reference side). Written by one design pass and kept as delivered, with local paths made repository-relative. Decision numbers inside predate PLAN-V3 §2 (D-P53 onward): follow that table. Where this memo and PLAN-V3 disagree, PLAN-V3 is the reconciled text. -->

# PLAN-V3 design memo — the reference side

Scratch directory (everything below is reproducible from it):
`docs/plans/V3-evidence/lean/reference/`

Run a scratch file with `run.sh <file>.lean` (it calls `lake env lean --root=<this directory>` from `formal/` with the scratch dir appended to `LEAN_PATH`). `RefModel.olean` and `RunLib.olean` live in scratch. Nothing was written into the repository.

**HEAD.** Start `6bde89f`, end `2cad8cc`. The task text says `f2fe99b`; `git diff --stat f2fe99b 6bde89f` and `6bde89f..2cad8cc` touch only `formal/docs/{ETA,QUEUE,STATUS,design}.md`. No Lean, fixture or Rust file changed, so every result holds at all three commits. `design.md:1917` now has a D-P51, so new decisions start at **D-P52**. Untracked `formal/docs/plans/REVIEW-V3.md` and `V3-evidence/` appeared during the session; they are not mine.

## 0. What was established

| # | Fact | Evidence |
|---|---|---|
| F1 | A computable decoder from coordinates into `G₁z` exists, and group operations on `G₁z` run in the VM (one r-torsion check 128 ms, one 255-bit scalar multiplication 85 ms). The PoseidonEnv header claim that decoding into `G₁z` is not computable is wrong. | `RefModel.lean`, `T1_Timing.lean` |
| F2 | The tree's own `prepare` (the body of `verifyNative`) at a real codec, real delta and real commitments returns `PANIC circuit.rs:2084` on the imported constraint system, and `Error.opening` once rotations are canonicalised. | `RunG.out` |
| F3 | With both repairs shimmed, the Lean pipeline matches `trace.json` on every compared value: 10 challenges, 72 reads, `assert_empty`, 1+45 MSM terms, `pairing_lhs`, `pairing_rhs`. | `RunABC.out`, run C |
| F4 | The comparison is sensitive: `delta := 2` changes exactly the `-G` scalar; one flipped evaluation bit changes the MSM; one flipped bit in `pi` gives `Error.transcript(Other)`. | `RunD.out`, `RunE.out` |
| F5 | On the real 49-query vector: value-keyed grouping fails, label-keyed grouping fails, slot-keyed grouping gives 40 commitments and 3 point sets. | `RunF.out` |
| F6 | A constructed pairing on `(G₁z, G2fold, G₁z)` depends on `[propext, Classical.choice, Quot.sound]` only, and so does a `Holds` exhibit at the computable codec. | `RefModel.out` |
| F7 | The payload's 19+8 commitment sections, omega, omega_inv, G1_BASE, G2_BASE and the DELTA literal equal the encodings of the real Lean-side data. The same checks fail at 19 identities and at `delta := 2`. | `D5.out` |
| F8 | The committed `proof.bin` and `trace.json` are one self-consistent run: Lean re-derives the logged read bytes and challenges from `proof.bin`. | `RunABC.out` |

Not established: that the Lean verifier **accepts** a Rust proof. The fixture SRS is Filecoin's (`srs_for_test` → `load_srs(SrsSource::Filecoin, …)`, `zk_stdlib/src/utils/plonk_api.rs:293`), so the trapdoor is unknown and the final check cannot be evaluated in any G1-only model.

## 1. Grouping repair (R-7 / E-1 / A-1)

### 1.1 The label is not a key

Rust builds one-piece references at these sites, read at this commit:

| Rust site | reference | label |
|---|---|---|
| `plonk/verifier.rs:605` | `&advice_commitments[column.index()]` (per proof) | `Advice(col)` |
| `plonk/verifier.rs:616` | `&committed_instances[column.index()]` (per proof) | `Instance(col)` |
| `permutation/verifier.rs:161,167,177` | `&self.coms.permutation_product_commitments[i]` | `NoLabel` |
| `logup/verifier.rs:183` | `&self.committed.multiplicities` | `NoLabel` |
| `logup/verifier.rs:192` | element of `self.committed.helper_polys` | `NoLabel` |
| `logup/verifier.rs:199,205` | `&self.committed.accumulator` | `NoLabel` |
| `trash/verifier.rs:70` | `&self.committed.trash_commitment` | `NoLabel` |
| `plonk/verifier.rs:640` | `&vk.fixed_commitments[column.index()]` | `Fixed(col)` |
| `permutation/verifier.rs:192` | element of `vkey.commitments` | `Permutation(i)` |
| `linearization/verifier.rs:96` | `Linear(points, scalars, labels)` | `Custom("linearization_poly")` |

Measured on the fixture's query vector:

```
label kind advice: 11 queries, 8 distinct allocations
label kind instance: 1 queries, 1 distinct allocations
label kind noLabel: 13 queries, 7 distinct allocations
label kind fixed: 15 queries, 15 distinct allocations
label kind vk_perm: 8 queries, 8 distinct allocations
label kind custom: 1 queries, 1 distinct allocations
one-piece queries at x whose commitment is the identity: 6 (labels [instance_0, fixed_8, fixed_10, fixed_11, fixed_12, fixed_16])
LABEL-keyed grouping: Error.opening
SLOT-keyed grouping:  ok, 40 commitments, 3 point sets of sizes [2, 1, 3]
VALUE-keyed grouping (tree): Error.opening
```

So an explicit allocation id is required. The `Linear` arm is already right: `Vec<&Commitment> == Vec<&Commitment>` dereferences, so points compare by value and labels are ignored.

**Premise P-ALLOC, to record in the plan.** Slot equality equals `std::ptr::eq` because each slot names one element of one live `Vec` (or one struct field) of a non-zero-sized type, borrowed for the whole of `multi_prepare`. For the committed instance this relies on the modelled caller: `test.rs:366` builds `let committed_pi = [identity]` as a fresh local. A caller that passed a slice of `vk.fixed_commitments` as the committed instance would alias; that is outside the modelled entry point.

### 1.2 Exact text

Typechecked as a patched copy in `D1_Grouping.lean` (types, `beq`, `asTerms`, `VerifierQuery.new`, `constructIntermediateSets` verbatim, `kzgCommitBeq`).

`formal/Midfall/Halo2/Exec/Query.lean`, new before `CommitmentReference` (:53):

```lean
inductive CommitSlot where
  | advice (proof col : Nat)
  | instance_ (proof col : Nat)
  | permProduct (proof set : Nat)
  | lookupM (proof lookup : Nat)
  | lookupHelper (proof lookup j : Nat)
  | lookupAcc (proof lookup : Nat)
  | trash (proof idx : Nat)
  | fixed (col : Nat)
  | sigma (i : Nat)
  | anon (n : Nat)
  deriving BEq, DecidableEq, Repr
```

`Query.lean:53-57`:

```lean
inductive CommitmentReference (F C : Type) where
  | onePiece (slot : CommitSlot) (com : C)
  | linear (points : Array C) (scalars : Array F) (labels : Array CommitmentLabel)
```

`Query.lean:70-75` (`CommitmentReference.beq`): the one-piece arm becomes `| .onePiece s _, .onePiece t _ => s == t`.
`Query.lean:84` (`asTerms`): `| .onePiece _ com => .ok #[(1, com)]`.
`Query.lean:106-108`:

```lean
def VerifierQuery.new {F C : Type} (point : F) (commitmentLabel : CommitmentLabel)
    (slot : CommitSlot) (commitment : C) (eval : F) : VerifierQuery F C :=
  { point, commitmentLabel, commitment := .onePiece slot commitment, eval }
```

`formal/Midfall/Halo2/Exec/Kzg/MultiOpen.lean:42-48`:

```lean
def kzgCommitBeq : CommitmentReference (Fr p) G₁ → CommitmentReference (Fr p) G₁ → Bool
  | .onePiece s _, .onePiece t _ => s == t
  | .linear p1 s1 _, .linear p2 s2 _ =>
      p1.size == p2.size && s1.size == s2.size &&
      (List.zip p1.toList p2.toList).all (fun (x, y) => decideBool (P.decEqG₁ x y)) &&
      (List.zip s1.toList s2.toList).all (fun (x, y) => x == y)
  | _, _ => false
```

The call at `MultiOpen.lean:257-259` and `constructIntermediateSets` (`Kzg/Utils.lean:123-195`) do not change. `addDummies` (:76-79) copies `o.commitment`, so it keeps the slot.

Producers. This text was not compiled as patched files; the slot order was validated at run time (49 slots for 49 queries, every slot agrees with its label).

- `Exec/Verifier.lean:757`: iterate `zipped` with its index `pi` (`List.zipIdx` yields `(x, i)`).
  - :770 `VerifierQuery.new … (CommitmentLabel.advice q.2.1.index) (.advice pi q.2.1.index) com ev`
  - :778 `… (CommitmentLabel.instance_ q.2.1.index) (.instance_ pi q.2.1.index) com ev`
  - :786 `pe.queries (p := p) pi vk.domain bf x`
  - :788-789 pass `pi` and the lookup / trashcan index
  - :798 `… (CommitmentLabel.fixed q.2.1.index) (.fixed q.2.1.index) com ev`
- `Exec/Permutation.lean:265` add `(proofIdx : Nat)`; :279-280 and :287 use `(.permProduct proofIdx i)`; :306 uses `(.sigma i)`.
- `Exec/Logup.lean:196` add `(proofIdx lookupIdx : Nat)`; :201 `(.lookupM proofIdx lookupIdx)`; :204-206 zip the helpers with their index `j` and use `(.lookupHelper proofIdx lookupIdx j)`; :208-211 `(.lookupAcc proofIdx lookupIdx)` twice.
- `Exec/Trash.lean:135` add `(proofIdx idx : Nat)`; :137 `(.trash proofIdx idx)`.

Pattern matches that gain a binder: `Logup.lean:391`, `Permutation.lean:555,605`, `Linearization.lean:145`, `Trash.lean:271`, `Verifier.lean:1237`, `Lowering/Snapshot.lean:101`, `Kzg/Utils.lean:267-270`.

KAT call sites that need a slot: `Verifier.lean:1220,1259,1280,1296`, `Snapshot.lean:497`, `Spec/Degrees.lean:531` (use `.anon` or map `ShapeCom`), `Instances/ChallengeStream.lean:139-143,272-276`. The ChallengeStream KATs reuse one commitment under two labels at two points and rely on value grouping: give both queries the same `.anon` slot to keep their pinned shape.

### 1.3 KATs (`D1_Grouping.lean`, all `true`)

- `fixtureShape_groups_ok`: instance_0 and fixed 8, 10, 11, 12, 16, all value 0 at one point, give six entries and one point set. (The task says five entries; with the committed instance it is six.)
- `fixtureShape_old_rejects_ok`: the value relation gives `Error.opening` on the same input.
- `duplicate_still_rejects_ok`, `duplicate_slot_distinct_values_rejects_ok`: the same slot twice at one point gives `Error.opening`, whatever the values.
- `oneSlotTwoPoints_ok`, `cisKats_ok`.

## 2. Rotation repair (E-6)

`formal/Midfall/Halo2/Exec/Circuit.lean:130-132` becomes (move `Rotation.int` up from `Exec/Domain.lean:85-94`):

```lean
inductive Rotation where
  | cur | next | prev | value (v : Int)

def Rotation.int : Rotation → Int
  | .cur => 0
  | .next => 1
  | .prev => -1
  | .value v => v

/-- rust: `pub struct Rotation(pub i32)` with derived PartialEq: equality of the integer. -/
instance : BEq Rotation := ⟨fun a b => a.int == b.int⟩
```

Direct users of the derived instance, measured with a `#direct_users` command over the `Midfall` namespace (12): `ConstraintSystem.{getAdviceQueryIndex, getFixedQueryIndex, getInstanceQueryIndex, queryAdviceIndex, queryFixedIndex, queryInstanceIndex}`, `instBEq{AdviceQuery, FixedQuery, InstanceQuery, VirtualCell}.beq`, `columnAny_kats_ok`, `convertSelectors_kats_ok`. Every later `deriving BEq` on a structure with a `Rotation` field picks the new instance up.

Two KAT clauses flip: `Circuit.lean:1892` (`(Rotation.cur == Rotation.value 0) == false` becomes `true`) and `:2083` (the second fixed query deduplicates, index `0`). Update the prose at `Circuit.lean:120-129`, `:2064-2067`, `PoseidonFixture.lean:144-147,184-186`.

Measured on `poseidonCs` (`D2_Rotation.lean`):

```
["fixed 9", "advice 0", "advice 1", "advice 2", "advice 3", "advice 4", "instance 0", "instance 1"]
today:    PANIC circuit.rs:2084, 2074 ×5, 2094 ×2
repaired: ["ok 0", "ok 0", "ok 1", "ok 2", "ok 3", "ok 4", "ok 0", "ok 1"]
```

A canonicalising importer was considered and rejected: every importer and hand-built constraint system would need it, plus a `Valid` clause. I used it only as the scratch shim.

Same class, one line: `Exec/VerifyingKey.lean:114-116` should read `vk.permutation.commitments.size = vk.cs.permutation.columns.size` (E-5 / H+2). It is 8 = 8 at the real key; the current form is 8 ≠ 3. Its only consumer is the refutation at `PoseidonValid.lean:413`.

## 3. Running the Lean verifier on the Rust proof

### 3.1 Computable models

- **Exponent model** (`Instances/ExponentModel.lean`): all three groups are `Multiplicative (ZMod p)`. It cannot hold a real proof's points (each would need a discrete log). The only `verifyNative = .ok` runs in the tree are Fr 17 fixtures here.
- **`G1Affine`** (`Instances/Bls12_381.lean`): a real 48-byte compressed codec, no group law.
- **Conformance replay** (`Conformance/Replay.lean`): event-driven; it never calls the verifier.
- **New, scratch `RefModel.lean`:** `G₁ := G₁z` (mathlib's `W.Point` over `ZMod blsP`, whose group law is computable), `G₂ := G2fold`, `Gₜ := G₁z`, `e(P,k) = k • P`. This runs everything except a pairing against an unknown trapdoor.

### 3.2 Results (`RunLib.lean` with drivers `RunABC`, `RunD`, `RunE`, `RunG`)

Every Exec function called is the tree's, unmodified: `parseTrace`, `Verifier.readAlgebra`, `Verifier.linearize`, `phaseA` (unpatched, to measure E-1), `MultiPrepare.buildQ`, `phaseB`, `phaseC`, `DualMSM.split`, `MSMKZG.eval`, `DualMSM.check`. Two shims stand in for the repairs:

- **S1:** the imported query lists are canonicalised (0, 1, −1 become `cur`, `next`, `prev`).
- **S2:** the tree's generic `constructIntermediateSets` is instantiated at `C := CommitSlot × G₁z` with slot equality.

| Run | Outcome |
|---|---|
| A. raw cs, tree grouping | stages 1-2 ok (theta, beta, gamma, trash_challenge, y, x agree); `linearize` fails: `PANIC proofs/src/plonk/circuit.rs:2084` |
| B. S1 only | `linearize` ok, 49 queries; `phaseA` fails: `Error.opening` |
| C. S1 + S2 | all compared values agree (below) |
| D. C with `delta := 2` | mismatch in exactly one term, `[44] -G` scalar |
| E. C with proof byte 1008 flipped | mismatch |
| F. C with proof byte 2639 flipped | `phaseC` fails: `Error.transcript(Other)` |
| G. C plus `DualMSM.check` at trapdoor 5 | terms agree; check returns `false` in about 3 s |

Run C, verbatim:

```
stage 1 parseTrace ok: pos=720, reads=15     ok theta, beta, gamma, trash_challenge, y
stage 2 readAlgebra ok: pos=2448, reads=67   ok x
stage 3 linearize ok: 49 queries
slots: 49 for 49 queries; every slot agrees with its label: true
stage 4a phaseA ok: 3 point sets of sizes [1, 2, 3], 3 q_coms    ok x1, x2, x3 (truncated), x4
stage 4 multiPrepare ok: pos=2640/2640, reads=72
ok read schedule (72 reads, widths and bytes)
ok assert_empty
ok dual_msm.left  (1 terms)
ok dual_msm.right (45 terms: label, scalar, point)
ok left.eval  (pairing_lhs)
ok right.eval (pairing_rhs)
[8622 ms] stage 6 MSM evaluated
=== C. canonical rotations + slot grouping: ALL COMPARED VALUES AGREE (rust verdict in trace.json: accept, pairing_check=true) ===
```

**Further divergences found once the two are repaired: none on this fixture.** Not exercised: any rejecting input, error-class fidelity, multi-proof, the `fewer-point-sets` branch, `snapshotOf`, the calldata leg, and E-8/E-9/E-10.

**What blocks the next step.** Only the final pairing check. `check_iff_g1` (`D6_Render.lean`, proved) shows that at the constructed pairing the check is `s • left = right` in `G₁z`. That is decidable in the VM once `s` is data.

### 3.3 The reference gate

- **Function:** `Midfall.Halo2.prepare E Features.solidity vk [[1]] [[inst]]` on `Transcript.initFromBytes proof`, then `assertEmpty`, `DualMSM.split`, `MSMKZG.eval`. Use the staged path (`parseTrace`, `readAlgebra`, `linearize`, `phaseA/B/C`) to name each challenge.
- **Model:** `G₁z`, `G2fold`, `G₁z` with the constructed pairing; `E := ⟨g1CodecC, poseidonFc, 7^(2^32), false⟩`; `vk` from `vk.json` and `cs.json` with commitments decoded into `G₁z`.
- **Comparison:** the 10 named squeezes; the read log (72 × width and bytes); 1+45 MSM terms as (label text, scalar BE, compressed point); `left_eval`, `right_eval`; the verdict class.
- **Expected values:** `trace.json` of the same bundle, written by `conformance_export.rs` from the real `prepare` run with `pairing_check = true`.
- **Falsifiers that must stay red:** run A's panic and run B's `Error.opening` until REF.1/REF.2 land; `delta := 2`; one flipped byte.
- **Acceptance half (test-SRS bundle):** `verifyNative E F (poseidonParamsAt s) vk inst proof = .ok ()`, plus the mutation corpus with matching error classes.
- **Cost:** about 9 s of VM time, so it fits a build-time `#eval … -- expect true` in `Instances/`. The proof bytes can be read from a `proof_hex` field (schema 2) or rebuilt from the 72 `wire_hex` reads, which cover all 2640 bytes.

## 4. The compressed codec (`RefModel.lean` §1-2)

```lean
def g1zOfPair? (pt : Nat × Nat) : Option G₁z :=
  if _hc : pt.1 < blsP ∧ pt.2 < blsP then
    if honc : affineOnCurve fpOps pt = true then
      if htor : blsR • emb ⟨pt, honc⟩ = 0 then
        some ⟨Multiplicative.ofAdd (emb ⟨pt, honc⟩), mem_zpowers_of_torsion ⟨pt, honc⟩ htor⟩
      else none
    else none
  else none

def g1zToCompressed (Q : G₁z) : Bytes := G1Affine.toCompressed (g1zAffine Q)

def g1zOfCompressedRaw? (b : Bytes) : Option G₁z :=
  (G1Affine.ofCompressed? b).bind fun P =>
    if P.isInfinity then some 1 else g1zOfPair? (P.x.val, P.y.val)

def g1zOfCompressed? (b : Bytes) : Option G₁z :=
  (g1zOfCompressedRaw? b).bind fun Q => if g1zToCompressed Q = b then some Q else none

def g1zOfEipC? (b : Bytes) : Option G₁z :=
  if b.size == g1Bytes then (g1Of? b).bind g1zOfPair? else none

def g1CodecC : G1Codec G₁z where
  ofCompressed? := g1zOfCompressed?
  toCompressed := g1zToCompressed
  toEip := g1zToEip
  ofEip? := g1zOfEipC?
```

Encoding: 48 bytes, big-endian x, top three bits of byte 0 are flags (bit 7 compression, always set; bit 6 infinity; bit 5 "y is the larger root"). Infinity is `0xc0` followed by 47 zero bytes. The decoder checks flags, canonical x, x ≠ 0, on-curve, and r-torsion.

**`torsion_eq_zpowers_gen` is confirmed** (`G1PointCount.lean:238`: `∀ X : W.Point, blsR • X = 0 → ∃ k : ℤ, k • emb genFrame = X`). It supplies the erased membership proof, so a decoder into `G₁z` is computable. Both placeholders (the constant-`none` decoder, the 19 identity commitments) were unnecessary.

Proved, standard three axioms:

- `g1zPair_of_g1zOfPair?` (decoder-first on coordinates) and `g1zOfPair?_g1zPair` (encoder-first on coordinates).
- `g1CodecC_ofEip : g1CodecC.ofEip? = g1CodecZ.ofEip?`. The computable decoder is the `Classical.choose` one, so every existing theorem about `g1CodecZ.ofEip?` transfers.
- `holds_transfer` and `holds_exhibited_C`.
- `g1CodecC_compressedRoundtrip` (decoder-first, by construction through the re-encode test).
- `g1CodecC_laws : G1CodecLaws g1CodecC`, given the width fact as a hypothesis.

Stated with `sorry` (the one law the headline needs and no frozen hypothesis supplies):

```lean
theorem g1CodecC_compressedEncoderFirst :
    ∀ Q : G₁z, g1CodecC.ofCompressed? (g1CodecC.toCompressed Q) = some Q
```

Its proof needs three pieces: `g1zOfPair?_g1zPair` (done); `fpSqrt` is a square root on squares (p ≡ 3 mod 4, `ZMod.euler_criterion`), so `rootFor x s` recovers y; and the flag bits are free because x < p < 2^381.

KATs (`D4_CodecKats.lean`): 50 points (19 fixed, 8 sigma, 21 proof, the committed identity, the generator). All four laws hold on each; the re-encode test is a no-op. Rejected: a curve point at x = 4 outside the r-torsion, x ≥ p, no compression flag, infinity with a tail, infinity with the sign bit, a short string. Flipping the sign bit gives the inverse point.

**If the noncomputable style is preferred instead** (decoder as `Classical.choose` over the encoder's image): decoder-first is `choose_spec` and encoder-first needs only injectivity of the encoder, which is easy if the sign bit is defined as `decide (y.val > (-y).val)`. The cost is that the headline's verifier is then not the function the gate runs. I recommend the computable codec.

## 5. Real key data (`D5_KeyData.lean`, `D6_Render.lean`)

```lean
def poseidonFixedCommitmentsReal : Array G₁z :=
  (decodeAll poseidonVkData.fixedCommitmentHex).getD #[]
def poseidonPermutationCommitmentsReal : Array G₁z :=
  (decodeAll poseidonVkData.permutationCommitmentHex).getD #[]
def frDelta : Fr blsR := (7 : Fr blsR) ^ (2 ^ 32)
def poseidonEReal : VerifierEnv blsR G₁z G2fold G₁z :=
  { g1 := g1CodecC, field := poseidonFc, delta := frDelta, fewerPointSetsRuntime := false }
def poseidonParamsAt (s : ZMod blsR) : ParamsVerifierKZG G₁z G2fold :=
  ParamsVerifierKZG.ofParams (g2foldExp 1) (Multiplicative.ofAdd s)
def poseidonRenderAt (s : ZMod blsR) : Render blsR G₁z G2fold G₁z   -- typechecks, computable
```

- **Delta.** Rust uses `F::DELTA` (`plonk/permutation.rs:276`); the generator emits `fr_delta_literal() = u256_string(fe_to_u256::<Fq>(&Fq::DELTA))` (`quotient_numerator/vm/mod.rs:4131`); `Fq` is the scalar field and `MULTIPLICATIVE_GENERATOR = 7` (`curves/src/bls12_381/fq.rs:531`). Lean computes `7^(2^32) = 0x08634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7`, and `poseidonInputs.frDelta = u256String (frWord frDelta)` evaluates to `true` (`false` at 2). The `Inv.lean:473-490` note that this is a base-field constant is wrong.
- **Transcript representation.** Keep `vk.transcriptRepr` imported from `vk.json` (R-1) and pinned by `EnvAgrees.vkDigestWord`. It reproduces Rust's challenges from the first squeeze onward (run C).
- **Modelled constructor.** `test.rs:378` calls `params.verifier_params()`, which is `ParamsVerifierKZG.ofParams`, not `read`.

The pins `EnvAgrees` lacks, typechecked generically as `KeyAgrees` (`D5_KeyData.lean`):

```lean
structure KeyAgrees (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁) (PV : PlanView)
    (params : ParamsVerifierKZG G₁ G₂) (encG2 : G₂ → Bytes) (frDelta : String) : Prop where
  fixedWords : PV.vk.fixedComms.map g1WordsBytes = vk.fixedCommitments.toList.map E.g1.toEip
  permWords : PV.vk.permutationComms.map g1WordsBytes =
    vk.permutation.commitments.toList.map E.g1.toEip
  omegaWord : headerWord? PV.vk "omega" = some (frWord vk.domain.omega)
  omegaInvWord : headerWord? PV.vk "omega_inv" = some (frWord vk.domain.omegaInv)
  g1Base : vkG1Words PV vkG1BaseSlot = E.g1.toEip P.g₁
  g2Base : vkG2Words PV vkG2BaseSlot = encG2 params.nG2Prepared⁻¹
  negSG2 : vkG2Words PV vkNegSG2BaseSlot = encG2 params.sG2Prepared⁻¹
  delta : frDelta = Midfall.Generator.QuotientFoldCompute.u256String (frWord E.delta)
```

Evaluated at the deployment data: `fixedWords`, `permWords`, `omegaWord`, `omegaInvWord`, `g1Base`, `g2Base`, `delta` are all `true`. `negSG2` is not decidable without the trapdoor. What is checkable holds: the payload's NEG_S_G2 x-coordinate equals `params.json`'s `s_g2` x-coordinate, and the bytes are not `−H2`, which refutes `sG2 := g₂` by bytes.

## 6. The curve assumption and Gap B

**What the Exec verifier reads.** `P.g₁` at exactly one site (`MultiOpen.lean:311`, the `-G` base; Rust `kzg/mod.rs:547` uses the curve constant `-E::G1::generator()`). `P.g₂` nowhere: `DualMSM.check` (`Kzg/Msm.lean:222-232`) reads only `params.sG2Prepared` and `params.nG2Prepared`. So the two G2 points are already data in Exec. Only `EnvAgrees.nG2` (`Inv.lean:573`) and the generator port (`Generator/Vk.lean:703,799,806`) mention class generators.

**Recommendation.**

1. **Replace the five axioms by a constructed instance.** Typechecked:

```lean
def eC : (Additive G₁z) →ₗ[ZMod blsR] (Additive G2fold) →ₗ[ZMod blsR] (Additive G₁z)  -- e(P,k) = k • P
instance pairingC : AdmissiblePairing G₁z G2fold G₁z where
  e := eC
  g₁ := g1zGen
  g₂ := g2foldExp 1
  …
theorem holds_exhibited_noAxiom : ∃ product, Eip2537.Holds g1CodecZ g2CodecFold product :=
  holds_staged (Gₜ := G₁z)
```

   `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `pairingC`, `holds_exhibited_noAxiom` and `holds_exhibited_C`. The generators are named, so `g1Base` and `g2Base` are computations and `EnvAgrees.nG2` is `rfl` (`poseidonRenderAt_generators`). No Exec change is needed. The digest G-2 claim is correct.

2. **The SRS point is data, bound by one hypothesis.**

```lean
def SrsEncodes (s : ZMod blsR) : Prop :=
  g2foldToEip (Multiplicative.ofAdd s)⁻¹ = poseidonNegSG2Bytes
theorem lowering_equivalence_poseidon_at (s : ZMod blsR) (hSrs : SrsEncodes s)
    (product : PairingProduct) : LoweringEquivalence (poseidonRenderAt s) product   -- stated, sorry
```

   For a known-trapdoor test SRS, `SrsEncodes s` is a closed computation (158 ms in the VM). For a real SRS it stays a hypothesis: true for the ceremony's `s`, and unprovable in the tree without cyclicity of the twist's r-torsion (G-3).

**Alternatives rejected.** Axioms pinning generator bytes are unnecessary once the instance is constructed. Proving G2 r-torsion cyclicity costs days and buys nothing the hypothesis does not. Making the G1 base an environment field is unnecessary because `P.g₁ = g1zGen` by `rfl`.

**What the headline then rests on.**

- Axioms: `propext`, `Classical.choice`, `Quot.sound`, plus the recorded `native_decide` axioms.
- Hypotheses: `DeploymentV2`, `EntryFrame` (trusted solc entry), `Eip2537.Holds g1CodecC ⟨g2foldToEip⟩ product`, `SoundSide` / `CompleteSide`, and `SrsEncodes s` for a real SRS only.
- `Holds` at the constructed pairing says, for the real EVM, exactly: G1ADD, G1MSM and MODEXP agree with `Externals.lean`, and PAIRING_CHECK on `(P₁, k₁H2), (P₂, k₂H2)` returns 1 iff `k₁P₁ + k₂P₂ = 0`. That is bilinearity and non-degeneracy on the r-torsion, the same content as before.

**Why the known-trapdoor fixture is worth a decision.** With the Filecoin SRS three things cannot be closed in Lean: acceptance of any honest proof (so the D-P45 non-vacuity witness), `KeyAgrees.negSG2`, and the ported generator's own SRS check (`srsTauIsConsistent`, `Generator/Vk.lean:701-704`). With a seeded `ParamsKZG::unsafe_setup` all three are computations. The current "deployment" is already a k = 6 test fixture (H-6).

## 7. The conformance corpus

Existing exporter: `proofs/solidity-verifier/tests/conformance_export.rs::export_poseidon_conformance_bundle` (feature `rust-verifier-trace`). It writes `vk.json`, `cs.json`, `params.json`, `instances.json`, `proof.bin`, `trace.json`. Schema 2 adds:

1. `params.json`: `srs_kind` (`filecoin` or `unsafe_setup`), `srs_seed`, `trapdoor_s_be_hex` (test SRS only; the test replays the same seeded RNG, draws `s`, and asserts `G2 * s == params.s_g2()`), the EIP-2537 256-byte forms of `g2`, `s_g2`, `-s_g2`, and the SRS file sha256.
2. `calldata.bin` and `evm.json` (revm result on that calldata) from the same run. The EVM leg is in `tests/m0_poseidon_regen.rs`.
3. `mutations.json`: for each single-bit mutation (one per read, plus truncation and a trailing byte), the Rust verdict and error class.
4. `proof_hex` and a `manifest.sha256` over the bundle files.
5. Optional: `g_lagrange_compressed_hex` (64 points), so the Lean `generateBaseVk` can be evaluated.

**Reproducibility (QUEUE R.5).** The non-determinism is `blind_quotient_limbs` drawing from `OsRng` (`proofs/src/plonk/prover.rs:126`); runs agree for the first 720 bytes only. The gate does not need byte-reproducibility:

- It compares Lean against the `trace.json` of the same bundle. The committed pair is self-consistent (F8).
- Acceptance is independent of blinding once the trapdoor is exported.
- The manifest pins the bundle as one run.

Seeding the prover would touch `proofs/src`, a baseline change, and is not needed.

A "genuine duplicate" corpus entry cannot come from Rust: `query_*_index` deduplicates at key generation, so `DuplicatedQuery` is unreachable from `prepare`. It stays a Lean KAT.

## 8. Milestones

- **M-R1, the reference runs:** REF.1, REF.2, REF.4, REF.5, REF.6, REF.8. Exit: the gate of §3.3 is green using tree functions only.
- **M-R2, the reference is pinned:** REF.3, REF.7, and the `Valid` integration (statement area).
- **M-R3, the reference accepts:** REF.9, REF.10, REF.11, REF.12.
- **Probes:** REF.13 (snapshot against `solidity_trace`), REF.14 (calldata leg).

## 9. Pitfalls for the implementer

- `lake env lean` does not apply `autoImplicit false`; every scratch file sets it.
- `parseTrace` exists twice (`Midfall.Halo2.parseTrace` and `Midfall.Conformance.parseTrace`); qualify it.
- `G₁z` has no `Inhabited` instance; use `[i]?`.
- Kernel `decide` on `W.Point` arithmetic is infeasible; use `#eval` or `native_decide` in `Instances/` only.
- Fermat-inverse byte folds and mathlib `nsmul` cost about the same here (142 ms against 128 ms).
- `poseidonVkCodecRoute` (`PoseidonEnv.lean:210`) is `rfl` about the placeholder and breaks when the real codec lands. Delete it.
- `check_frozen_axioms.py:126-131` and `check_hypothesis_bundles.py:130` hard-code the five axioms; they change in the same commit as the swap.
- KAT totals pinned by `kat_gate.py` move with each new `#eval … -- expect`.
- Do not report the shimmed run C as a tree result. Until REF.1 and REF.2 land, the tree's `prepare` returns a panic or `Error.opening` (F2).

Please review the accuracy and completeness of this memo before relying on it.
