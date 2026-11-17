# Decisions pending human sign-off — drafts (2026-11-17)

Drafted in a review of `formal/baseline...7bf0497`. **Nothing here is in force.** For each item:
fill in the decision and the sign-off line, then record it in `design.md` (the PROPOSED entry for
D-P45–D-P49, or the next free D-P number for the others) and delete it here. The orchestrator must
not act on an item without a sign-off line (EXECUTION-V2 W2). Sign-off format:
`Signed off: <name>, <date>, <where: message / commit / PR>`.

## 1. W2: are there orchestrator decisions on delegated authority?

D-P45–D-P49 cite a "standing delegation" (2026-11-17); W2 says *"there are no orchestrator decisions
on delegated authority"*, and no grant is recorded anywhere.
- **Recommended: keep W2.** D-P45–D-P49 stay PROPOSED until each is signed below.
- Alternative: amend W2 and the GOAL prompt with a bounded grant. For example, the orchestrator
  may approve changes to REFINABLE §6/§7 shapes that only strengthen proof obligations and come with
  a landed witness and falsifier; frozen-surface, scope and fixture changes stay human-only.

Decision: ______ · Signed off: ______

## 2. R-72's second question: add `hR : R.Valid` to `LoweringEquivalence`?

The orchestrator recommended it before C.4; it was never decided and still sits in Q0.5.
- **Recommended: reject.** `¬ poseidonRender.Valid` is proved (PoseidonValid.lean:468), so with
  `R.Valid` as a hypothesis the headline is provable by contradiction with an empty cone. PLAN-V2 §6
  requires the headline "with no other hypotheses". Plan/VK coherence is already certified where it
  belongs: DONE requires `poseidon_valid` to be proved.

Decision: ______ · Signed off: ______

## 3. D-P45: repair `HypothesesInhabited` (frozen, Statements.lean:269)

- **Recommended: approve, with this exact text** (two conjuncts added):

```lean
def HypothesesInhabited (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∃ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W H vkAddr ∧ EntryFrame R W Lyt H cd st₀ ∧
      Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product ∧ SoundSide R H cd ∧ CompleteSide R H cd ∧
      LeanAccepts R H cd ∧ G1CodecLaws R.E.g1
```

- Why these two. They are exactly the remaining antecedents of the headline's conjunct 2, so
  headline ∧ gate implies an honest run exists and returns ABI `true` at the witness. That is the
  non-vacuity R-72 asked for, without stating a run as a hypothesis. `gate_weak` dies because
  `LeanAccepts` forces decoding to succeed, and the bare selector never decodes (`sel_nondecode`).
- D-P45 as written also adds a run-existence conjunct. Given the headline that is redundant, and
  it would make the gate need a whole-program run proof of its own. Choose this variant only if you
  want the gate to certify a run without the headline.
- Cost to know. Discharging the gate at the deployment needs an accepting calldata. REVIEW.md:3019
  records none at any model in the tree, and the decoder is `Classical.choose`
  (G1Agreement.lean:1995), so it will be proved, not evaluated. Q0.5 must first re-create R-72's
  reproducer, which was lost with `/tmp/q04`.

Decision: ______ · Signed off: ______

## 4. D-P46: VK base-slot pins in `Render.Valid` (frozen §2)

- **Recommended: approve in principle, extended, and applied only after #8.**
  - Extend to all three base pins v1 had. v1 restored the same three once already (P-RESTORE2,
    Inv.lean:513); V2 dropped all three and D-P46 restores two.
  - Hold until Gap B is decided. At the deployment the second pin reads `NEG_S_G2_BASE =
    encG2 g₂⁻¹` (−G₂) while the payload holds −s·G₂, so applying it now adds a clause that cannot
    hold at this render.
- Draft clause (G2 halves as `fpG2Slots`, FinalPairing.lean:234; G1 half as v1's Inv.lean:617,
  whose `P.g₁` is v1's spelling of the pairing's G1 generator, so the V2 spelling is for the card):

```lean
  baseSlots : vkG1Words R.pv vkG1BaseSlot = R.E.g1.toEip P.g₁ ∧
    vkG2Words R.pv vkG2BaseSlot = R.encG2 (R.params.nG2Prepared)⁻¹ ∧
    vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 (R.params.sG2Prepared)⁻¹
```

Decision: ______ · Signed off: ______

## 5. D-P47: re-export the fixture before porting `LoweringPlan::new`

- **Recommended: approve the ordering** (reordering is within the orchestrator's re-planning,
  EXECUTION-V2 §6), **and confirm the scope point yourself.** A refreshed fixture must be the same
  deployed circuit and VK; D.1's byte-for-byte gate must still pass. QUEUE R.1 stops otherwise.
- Know the limit. It cannot clear `codegen` (WP-G1, QUEUE R.2), `model` (#9) or Gap B (#8), and
  `poseidon_valid` needs all of them.

Decision: ______ · Signed off: ______

## 6. D-P48: `RETURN_MPTR` pin in `Render.Valid` (frozen §2)

- **Recommended: approve.** Clause: `returnMptr : ∃ m, R.consts.lookup "RETURN_MPTR" = some m` (T.1's
  `trRetMptr`). `tr_blockProgress` needs it, so without it the TraceReturn row cannot come from
  `R.Valid`. The deployment value (4096) is prose today; QUEUE F.2 records it as a command output.

Decision: ______ · Signed off: ______

## 7. D-P49: gate `BlockSound`'s poisoned arm on `q ≠ .traceReturn` (refinable §6)

- **Recommended: approve, conditional on QUEUE S.3 step 1.** If `tr_sound_clean'` and
  `tr_poison_walk'` do not elaborate sorry-free, D-P49 falls. The reasoning checks out:
  `slices_seq_sound`'s post has no `normal ∧ Poisoned` arm (Blocks.lean:307), and `isRevertOrHalt`
  excludes running off the end (Bridge.lean:552). So rejecting option (a) is correct.

Decision: ______ · Signed off: ______

## 8. Gap B: how s·G₂ is modelled at the deployment (QUEUE R.4)

`poseidonSG2 := bls12_381Pairing.g₂`, "NOT checked against that hex" (PoseidonEnv.lean:386). The
deployment's Lean verifier therefore pairs with g₂ where the contract pairs with s·G₂. Neither D-P46
nor FP.0's `fpG2Slots` can hold at this render as modelled.
- **(a) Recommended:** name both G2 bases from their bytes, as `g1zOfEip?` already does for G1:
  `Classical.choose` on `∃ x, encG2 x = <bytes>`. Then set `nG2Prepared`/`sG2Prepared` from them, so
  the slot pins follow from `choose_spec`.
  - No new axiom. It does need proofs that the bytes lie in the encoder's image.
  - The pins become proved rather than computed, so `Valid`'s "decided by computation" docstring
    (Statements.lean:136) needs a recorded exception.
- (b) An axiom pinning them. This adds an assumption beyond PLAN-V2 §6's axiom list, so §6 changes.
- (c) Rescope. State that FinalPairing is not tied to the deployment's VK in the English headline.
- Decide `g1CodecZ.ofCompressed?` (same discrete-log class, blocks `end_to_end`) at the same time.

Decision: ______ · Signed off: ______

## 9. `Valid.model`: make it dischargeable (QUEUE R.3)

C.4 found it true but blocked: `poseidonModelVal`'s error arm mentions `poseidonModel` in its own
proof type.
- **(a) Recommended:** a one-line, recorded exception to "do not edit v1 .lean files": `deriving
  Inhabited` on `Halo2Verifier`, plus a `getD` restatement. No statement changes.
- (b) A frozen-surface change to `Render.Valid.model`.

Decision: ______ · Signed off: ______

## 10. WP-T: automation before block proofs?

PLAN-V2:269 says WP-T comes "BEFORE M1" because "hand proofs at that density are infeasible". Its
accept line is: re-prove TraceReturn in under 100 lines, and record lines per token. T.2 declined
the tactic, TraceReturn took 988 lines by hand, and S.4–S.6 queue more hand proofs.
- **(a) Recommended:** keep WP-T ahead of the loop-heavy rows (S.5, S.6) with PLAN-V2:278's accept
  line. S.4 (one statement) may go by hand as the tactic's second test.
- (b) Drop WP-T, and re-estimate from TraceReturn's measured lines per token.

Decision: ______ · Signed off: ______

## Also open (no decision needed yet)

- `Rejects`/`SoundSide` (C.2). Keep it an investigation (C.3). D-P47's refusal to weaken it to
  move the cone was right.
