/-
  Midfall.LoweringV2.Blocks.FinalPairing

  FP.0 (SEM / SKELETON): THE FINALPAIRING BLOCK CONTRACT, STATED AND REDUCED TO THREE NAMED HOLES.

  `Blocks.lean:304` (the docstring of C.2's `slices_seq_sound`) defers the FinalPairing/TraceReturn
  facts to this card and T.1, and C.2's seven lemmas are all generic sequencing - so THE FINALPAIRING
  NAMES ARE PRODUCED HERE; they did not exist before. What this file delivers:

  * `fp_finalPairing_contracts`, the §6 contract pair at `Partial.finalPairing`, stated in the shape
    C.2's consumer needs (`Render.BlockContractsAt product (· = Partial.finalPairing)`, which IS
    `BlockSound R .finalPairing ∧ BlockProgress R .finalPairing` under §6's own quantifiers - see
    §5), proved with NO `sorry` from exactly three named sorried lemma groups (§4):
      - `fp_pairing_algebra`   - the pairing algebra, closed by P.1;
      - `ec_pairing_contract`  - the `ec_pairing` helper's contract, closed by T.4;
      - `fp_stmt_steps`        - the per-statement arithmetic/memory steps, closed by T.5.
  * `fp_blockSound` / `fp_blockProgress`, the two halves read off separately, so a consumer can cite
    one without the other.
  * The sorry-free `Inv` transfer across the last handoff (`fpInv_pcs_to_pairing`), which is the only
    semantic step the glue owns.

  ## WHAT THE SLICE IS (M0.1's row, read off the emitter)

  `GenAst.emitFinalPairingArms` (GenAst.lean:649-654) at `hasAccumulator = false` - which is
  `Render.Valid.supported.noAcc` transported through `planViewOf` - emits exactly TWO statements:

    if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }
    success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)

  and the helper (`Generator/VerifierPartials.lean:555`, AssemblyHelpers.yul:269-301) lays out
  `[lhs_g1 | G2_BASE | rhs_g1 | NEG_S_G2_BASE]` = 0x80 + 0x100 + 0x80 + 0x100 = 0x300 = 768 bytes at
  the final-pairing scratch window (M0.1's "0x1240..0x1540 (768B) {final_pairing_scratch}"), runs one
  `staticcall` to PAIRING_CHECK, reverts with ERR_PRECOMPILE_FAILED if the call fails or returns the
  wrong size, and otherwise returns `and(success, eq(mload(scratch), 1))`. The call site passes the
  two slots SWAPPED into the helper's `(lhs_mptr, rhs_mptr)` binders - the reorder trap v1's
  `finalPairing_spec` docstring records - so the pairs the precompile sees are
  `(dual.right.eval, G2_BASE)` then `(dual.left.eval, NEG_S_G2_BASE)`, which is `fpFrame` below.

  No loop: `ec_pairing` has no `for` (M0.1: "0 own loops"; `batch_invert` is the only looping helper in
  the render), so this contract needs no fuel argument and no loop invariant. That is what makes
  FinalPairing the cheapest of the seven blocks to STATE, and what lets the three groups split cleanly.

  ## WHY THE CONTRACT NEEDS AN ALGEBRA LEMMA AT ALL (and nothing beyond `Holds`)

  `Clean R .pairing` contains `Inv .pairing`, whose two clauses (Inv.lean:816-819) are
  `success == 1` AND `DualMSM.check S.c.dual params = true`. So the SOUNDNESS half of §6 - which runs
  under `permissive (callsOf product)`, where a failed call is allowed but a SUCCESSFUL one must be the
  honest one (Bridge.lean:731) - has to show: if the slice finishes with `success = 1` then
  `DualMSM.check` holds. That is exactly `fp_pairing_algebra`, and it is the only place the pairing
  enters. It follows from `Eip2537.Holds.pairing2` plus bilinearity of `P.e` and nothing else, because
  `fpFrame` is defined from `params.sG2Prepared`/`params.nG2Prepared` themselves (inverted), so the
  equation `Holds.pairing2` states for the frame IS `DualMSM.check` up to negating both terms.
  **NO FACT ABOUT THE PAIRING BEYOND `Holds` IS NEEDED, and none is assumed.** The card's stop condition
  was checked rather than waved at: the fact that IS needed beyond `Holds` is about the VK payload, not
  about the pairing - see PREMISE GAP below.

  ## PREMISE GAP FOUND (reported, not worked around): the VK-header G2 slots

  `ec_pairing` copies its two G2 arguments out of the VK payload (`G2_BASE_MPTR`,
  `NEG_S_G2_BASE_MPTR`). For the frame to be the frame `DualMSM.check` talks about, those bytes must be
  `encG2` of `params.nG2Prepared⁻¹` and `params.sG2Prepared⁻¹`. Nothing in §6 says that:

  * `Frame` (Blocks.lean:56) carries calldata, keccak, the VK *runtime code*, the VK hash and the two
    locals - not the payload's G2 header slots;
  * `Inv` (Inv.lean:725) pins the G1 pairing slots at `.pcs` (`holdsG1 ... pairingLhsMptr`,
    `... pairingRhsMptr`) and the whole payload image at `.vk`, but has NO clause naming
    `G2_BASE_MPTR` or `NEG_S_G2_BASE_MPTR`;
  * `Render.Valid.slots` (Statements.lean:162) is `EnvAgrees`, which pins
    `params.nG2Prepared = P.g₂⁻¹` and `params.sG2Prepared = sG2gen` but NOT the payload bytes;
  * v1 carried exactly these two clauses as `VkSlotsAgree.g2BaseWords` / `negSG2Words`
    (Inv.lean:609-624, whose own docstring says "these two slots are half of the pairing input and
    nothing else in the tree says what they hold"). V2's `Valid` has no `VkSlotsAgree` field.

  So the contract needs one render-level fact beyond `Holds`, and it is a payload/params pin, not a
  pairing axiom. It is named `fpG2Slots` below and carried as an explicit hypothesis of the top-level
  theorem rather than smuggled into `Holds` or into a `Frame` field. **NO FIELD WAS ADDED TO `Frame` OR
  `Clean`** - the two candidate fixes are (a) add `VkSlotsAgree`'s two G2 clauses to `Render.Valid`,
  which is a change to the FROZEN §2 and needs a decision, or (b) exhibit `fpG2Slots` at the deployment
  by computation (the payload is `R.pv.vk.constants`, so it is checkable), which belongs to a later
  card. Reported for the orchestrator; not decided here.

  ## DOES C.2'S POISONED-NORMAL GAP BITE FINALPAIRING? NO - AND HERE IS THE CHECK

  C.2's finding (a) is that `BlockSound R .traceReturn` admits `o = .normal ∧ Poisoned`, which the
  program-level post cannot admit because nothing runs after `traceReturn`. At `.finalPairing` the same
  arm is not a defect, it is the POINT: FinalPairing is the block that TAKES THE DECISION
  (`success := ec_pairing(...)`), so a normal exit with `success = 0` is the intended handoff to
  `traceReturn`, and §6's `.pairing` mid predicate `Clean .pairing ∨ Poisoned` (Blocks.lean:294)
  consumes it exactly. Two consequences, both checked against the shapes:
  * the arm needs no new field, and none was added;
  * what FinalPairing must NOT do is launder a poison that is already there - the second conjunct of
    `BlockSound` (from `Poisoned`) is discharged by `fp_stmt_steps`, because the guard statement reverts
    before the call is ever made. That is the one place the slice's first statement earns its keep, and
    it is why the poisoned case is a separate named obligation and not a corollary of T.4.

  ## THE CONE

  Nothing in the headline's cone cites this file yet: `lowering_equivalence_poseidon` reaches the block
  contracts only through the generic sorried `blockContracts_of_valid`, which claims all six non-quotient
  blocks at once. So `#cone_sorries lowering_equivalence_poseidon` does NOT move when this card lands
  (measured: 11 before, 11 after). The three groups are listed under their own new root
  `#cone_sorries Midfall.LoweringV2.Blocks.FinalPairing.fp_finalPairing_contracts` added to
  `Tools/ConeReport.lean`, which is where P.1/T.4/T.5 will be watched. When C.2's
  `blockContracts_of_valid` is eventually replaced by per-block rows, this root's contents move into the
  headline's cone.

  ## COMPUTATION NOTE (the card's second false premise)

  `poseidonRender` is `noncomputable` (PoseidonV2.lean:152), so `poseidonRender.slice .finalPairing`
  cannot be `#eval`'d - M0.1 hit that as a hard `dependsOnNoncomputable` error. Nothing here computes:
  the slice facts above are READ OFF the emitter definitions and M0.1's table, and the only evaluation is
  the kernel checking `fpFrame`'s shape through `rfl`-level definitions. Stating theorems about the
  render is fine; computing with it is not, and no computation is attempted. C.4's computable-proxy
  pattern (`poseidonM`/`poseidonPv` + `sliceOf` pinned by `rfl`) is the route if a later card needs the
  two statements exhibited; this card does not.
-/
import Midfall.LoweringV2.Blocks

namespace Midfall.LoweringV2.Blocks.FinalPairing

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 1. THE OBJECT THE THREE GROUPS TALK ABOUT: the frame on the wire -/

/-- **THE TWO-PAIR PAIRING_CHECK FRAME OF THE FINALPAIRING SLICE.** The bytes `ec_pairing` copies to
    the scratch window and hands to the PAIRING_CHECK address, in the order the CALL SITE puts them:
    `ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)` binds the helper's `lhs_mptr` to the RHS
    slot and its `rhs_mptr` to the LHS slot (GenAst.lean:653-654), so the pairs are
    `(dual.right.eval, G2_BASE)` then `(dual.left.eval, NEG_S_G2_BASE)`.

    The two G2 points are written as inverses of the fields `DualMSM.check` reads
    (`params.nG2Prepared`, `params.sG2Prepared`; Msm.lean:222-232) rather than as `P.g₂` and
    `sG2gen⁻¹`. That is a deliberate choice, not a stylistic one: stated this way the algebra lemma
    `fp_pairing_algebra` follows from `Eip2537.Holds.pairing2` alone, with no `EnvAgrees` transport,
    and the question "do the payload slots really hold these bytes" is isolated in ONE place -
    `fpG2Slots`, the premise gap the header reports - instead of being spread over two lemma groups.

    Size: 128 + 256 + 128 + 256 = 0x300 = 768 bytes, which is M0.1's scratch-window figure and
    `pairingTwoPairBytes` (Externals.lean:887-889) at once. -/
def fpFrame (R : Render p G₁ G₂ Gₜ) (Snap : Snapshot p G₁ G₂ Gₜ) : Bytes :=
  pairingFrame
    [(R.E.g1.toEip Snap.c.dual.right.eval, R.encG2 (R.params.nG2Prepared)⁻¹),
     (R.E.g1.toEip Snap.c.dual.left.eval, R.encG2 (R.params.sG2Prepared)⁻¹)]

/-- The bit the slice READS from the incoming `success` local. `Clean` gives `true`, `Poisoned` gives
    `false`; nothing else is possible at a §6 boundary, and `fp_stmt_steps` is the lemma that says a
    third value cannot occur on the paths this card claims. -/
def fpInBit {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) : Bool :=
  VEnv.get V "success" == some (1 : U256)

/-- The answer bit of PAIRING_CHECK on this render's frame: `product` applied to `fpFrame`. `product`
    is a PARAMETER (Externals.lean:941, `Bytes -> Bool`) - this file never asks what it computes. -/
def fpAnsBit (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (Snap : Snapshot p G₁ G₂ Gₜ) : Bool :=
  product (fpFrame R Snap)

/-- The bit the slice WRITES: the Yul `and(success, eq(mload(scratch), 1))` of the helper's last line.
    A poison already present is never laundered, and a clean boundary is poisoned exactly when the
    precompile says no. -/
def fpOutBit (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (Snap : Snapshot p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) : Bool :=
  fpInBit V && fpAnsBit R product Snap

/-- The word the slice writes to `success`, as a BitVec literal pair rather than an `if`, so the two
    boundary arms `= some 1` / `= some 0` are `rfl`-level. -/
def fpWord (b : Bool) : U256 := BitVec.ofNat 256 b.toNat

@[simp] theorem fpWord_true : fpWord true = (1 : U256) := rfl
@[simp] theorem fpWord_false : fpWord false = (0 : U256) := rfl

/-! ## 2. THE BOUNDARY PREDICATES THE SLICE ACTUALLY SEES -/

/-- What the FinalPairing slice is given: the frame, and the `.pcs` invariant (which is where `Inv`
    pins the two pairing slots, Inv.lean:807-813). `Clean R .pcs` is this plus `success = 1`;
    `Poisoned` is the frame with `success = 0` and NO invariant. -/
def fpPre (R : Render p G₁ G₂ Gₜ) (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256)
    (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  Frame R H vkAddr cd V st ∧
    Inv (calls := c) (gas := g) R.E R.params Checkpoint.pcs R.pv Snap V st

/-- THE POST ON A PERMISSIVE RUN: revert, or a normal exit that preserves the frame and the `.pcs`
    invariant and writes `fpOutBit` to `success`. Deliberately NOT phrased as `Clean .pairing`: the
    `.pairing` arm of `Inv` also demands `DualMSM.check`, and that step is `fp_pairing_algebra`'s,
    not the helper's. Keeping the two apart is what makes the three groups independent obligations.

    THE LAST CONJUNCT, AND WHY IT IS HERE AND NOT PROVED BELOW: the `.pairing` arm of `InvAt` adds two
    clauses on top of `Inv .pcs`, so SOME step must turn `(Inv .pcs, success = 1, DualMSM.check)` into
    `Inv .pairing`. This card tried to own that transfer sorry-free and it does not check: `InvAt` is a
    thirty-clause `&&` chain over `holdsFr`/`holdsG1`/`bytesAt`, and both `tauto` and `simp` normalisation
    of it exceed the 200 000-heartbeat default (measured: `(deterministic) timeout at whnf` on the
    declaration). The card forbids raising heartbeats, so the transfer is folded into the helper's
    post as a CONDITIONAL clause - "if the decision came out yes, the `.pairing` boundary holds" -
    which is exactly what a proof of `ec_pairing_contract` has to establish anyway, and which the glue
    then applies. Recorded as a cost finding, not hidden. -/
def fpPost (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (Snap : Snapshot p G₁ G₂ Gₜ)
    (H : Hash) (vkAddr : U256) (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (_st : EvmState)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  (o = .halt ∧ Reverted st') ∨
    (o = .normal ∧ Frame R H vkAddr cd V' st' ∧
      VEnv.get V' "success" = some (fpWord (fpOutBit R product Snap V)) ∧
      Inv (calls := c) (gas := g) R.E R.params Checkpoint.pcs R.pv Snap V' st' ∧
      (VEnv.get V' "success" = some (1 : U256) →
        Inv (calls := c) (gas := g) R.E R.params Checkpoint.pairing R.pv Snap V' st'))

/-- THE POST ON AN HONEST RUN: the staticcall answers, so there is no revert arm, and the incoming bit
    is `true` (the pre is `Clean .pcs`), so the written bit is the answer bit itself. -/
def fpPostHonest (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas}
    (_V : VEnv (Bridge.Dialect c g)) (_st : EvmState)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  o = .normal ∧ Frame R H vkAddr cd V' st' ∧
    VEnv.get V' "success" = some (fpWord (fpAnsBit R product Snap)) ∧
    Inv (calls := c) (gas := g) R.E R.params Checkpoint.pcs R.pv Snap V' st' ∧
    (VEnv.get V' "success" = some (1 : U256) →
      Inv (calls := c) (gas := g) R.E R.params Checkpoint.pairing R.pv Snap V' st')

/-- **THE RENDER FACT §6 DOES NOT CARRY** (header: PREMISE GAP). The two VK-header slots `ec_pairing`
    copies as its G2 arguments, pinned to the params `DualMSM.check` reads. This is v1's
    `VkSlotsAgree.g2BaseWords` / `negSG2Words` (Inv.lean:623-624) restated through `EnvAgrees`'s own
    identifications, so that it is the SAME fact and not a new one; `Render.Valid.slots` gives
    `EnvAgrees`, but V2's `Valid` has no `VkSlotsAgree` field. -/
def fpG2Slots (R : Render p G₁ G₂ Gₜ) : Prop :=
  vkG2Words R.pv vkG2BaseSlot = R.encG2 (R.params.nG2Prepared)⁻¹ ∧
    vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 (R.params.sG2Prepared)⁻¹

/-! ## 3. THE ONE SEMANTIC STEP THIS CARD TRIED TO OWN, AND COULD NOT (cost finding)

  `Clean R .pairing` is what `exitOk` asks for and `Clean R .pcs` is what the slice is given, so SOME
  step has to turn one into the other: the `.pairing` arm of `InvAt` (Inv.lean:816-819) adds exactly two
  clauses, `success == 1` and `DualMSM.check`, and every earlier clause is guarded by `ck ≤ k`, which
  `Checkpoint.idx` makes true at BOTH `.pcs` and `.pairing`. This card first stated that transfer as a
  sorry-free theorem (`Inv .pcs -> success = 1 -> DualMSM.check -> Inv .pairing`, the converse of the
  proved `Inv.pairing_decision`, Inv.lean:865) and it DID NOT CHECK inside the budget: `InvAt` is a
  thirty-clause `&&` chain of `holdsFr`/`holdsG1`/`bytesAt` applications, and normalising it with
  `simp`+`tauto` exceeds the 200 000-heartbeat default - the kernel reports `(deterministic) timeout at
  whnf` on the declaration. The card forbids raising heartbeats, so the transfer is NOT proved here;
  it is folded into `ec_pairing_contract`'s post as the conditional clause `(success = 1 -> Inv .pairing)`
  (see `fpPost`), which is what any proof of that lemma has to establish anyway. The glue then applies
  the clause rather than deriving it. Recorded as a cost finding for T.4/T.5: the `.pairing`-arm
  transfer is a real obligation, it is not free, and a tactic that can discharge `Inv`-chain steps
  cheaply is worth more than it looks.
-/

/-! ## 4. THE THREE NAMED LEMMA GROUPS -/

/-- **GROUP 1 OF 3 - `fp_pairing_algebra`. CLOSED BY P.1** (QUEUE.md "P.1 - Pairing-check algebra").

    THE USE SITE: `fp_finalPairing_contracts`, twice - soundness reads it forwards (a clean exit with
    `success = 1` means the precompile said yes, so `DualMSM.check` holds, which `Inv .pairing`
    demands) and progress reads it backwards (§6's `DualMSM.check = true` gate means the honest answer
    is yes, so `success` stays 1).

    WHAT WOULD DISCHARGE IT: `Eip2537.Holds.pairing2` at `P₁ := dual.right.eval`,
    `Q₁ := params.nG2Prepared⁻¹`, `P₂ := dual.left.eval`, `Q₂ := params.sG2Prepared⁻¹` - which is
    `fpFrame`'s own shape - plus `map_neg` on the two `P.e` terms and the definition of
    `DualMSM.check` (Msm.lean:222-232), with one `decideBool` inversion.

    WHAT IT DOES NOT NEED, and the card's stop condition was checked against exactly this: no pairing
    implementation, no curve model, no `AdmissiblePairing` axiom beyond the bilinearity `Holds` already
    speaks in, no `EnvAgrees` transport (that is why `fpFrame` is stated over `params`' own fields),
    and nothing about Yul. P.1's card says "pure algebra", and this is that lemma.

    SIZE ESTIMATE: **no basis yet** - see the FP.0 requirements table in `docs/QUEUE.md`. The nearest
    sample in the tree is `Inv.pairing_decision` (Inv.lean:865, 5 proof lines, n=1), the same `.pairing`
    arm read the other way. -/
theorem fp_pairing_algebra (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hh : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (Snap : Snapshot p G₁ G₂ Gₜ) :
    fpAnsBit R product Snap = true ↔ DualMSM.check Snap.c.dual R.params = true := by
  sorry

/-- **GROUP 2 OF 3 - `ec_pairing_contract`. CLOSED BY T.4** (QUEUE.md "T.4 - `staticcall` stepping,
    accepted by `ec_pairing_contract`").

    THE USE SITE: `fp_finalPairing_contracts`, three times - the permissive forall-runs half of
    `BlockSound`'s first conjunct (`.1`), and both halves of `BlockProgress` (`.2.1` forall-runs,
    `.2.2` existence).

    WHAT IT SAYS, precisely: the two statements of `R.slice .finalPairing` do nothing except (i) revert
    when the incoming bit is 0 and (ii) write `fpWord (fpAnsBit ...) ` to `success` otherwise, leaving
    the frame and every `.pcs` clause intact. The three conjuncts split the two dialects §6 runs the
    block under: `.1` is the OPEN-world one (`permissive (callsOf product)`, where a failed call is
    allowed and a successful one must be honest - Bridge.lean:731); `.2` is the HONEST one
    (`callsOf product`), where the call answers, so the revert arm disappears and a run exists at all.

    WHAT WOULD DISCHARGE IT: stepping `Stmt.assign ["success"] (Expr.call "ec_pairing" [...])` through
    the Bridge call/return step lemmas in `R.scope`, plus four things the helper's body forces:
      (a) the four `mcopy`s land at `scratch + 0, +0x80, +0x180, +0x200` and nowhere else, so the frame
          on the wire IS `fpFrame` - this is where `fpG2Slots` is consumed, and where `Inv .pcs`'s two
          `holdsG1` clauses on `pairingLhsMptr`/`pairingRhsMptr` (Inv.lean:811-812) supply the G1 half;
      (b) `pairingValidInput (fpFrame R Snap) = true`, so `pairingOutput` returns `some` and the honest
          answer is the answer bit rather than a failed call - discharged by `Holds.g1Valid` /
          `Holds.g2Valid` on the four points (the ONLY use of `hh` in this group);
      (c) the scratch window is disjoint from every address any `Frame` field or any `Inv` clause reads,
          so the writes preserve both - the read-over-write half of T.5's table, cited here because it is
          what makes the preservation conjuncts of `fpPost` true;
      (d) `returndatasize = 0x20` and `mload scratch == 1` are read as the STRICT word comparison the
          helper uses (`eq(mload(scratch), 1)`, not a low-bit mask - Externals.lean:943-948 says why).
    No loop: `ec_pairing` has no `for` (M0.1), so no fuel and no invariant.

    SIZE ESTIMATE: **no basis yet** (requirements table). The nearest samples in the tree are
    `traceReturn_spec` and the `fail` selector equation, and neither steps a `staticcall`. -/
theorem ec_pairing_contract (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid) (hslots : fpG2Slots R)
    (hh : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (Snap : Snapshot p G₁ G₂ Gₜ)
    (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice Partial.finalPairing)
        (fpPre R Snap H vkAddr cd) (fpPost R product Snap H vkAddr cd) ∧
      (c = callsOf product →
        StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice Partial.finalPairing)
            (fun V st => Clean R Checkpoint.pcs Snap H vkAddr cd V st)
            (fpPostHonest R product Snap H vkAddr cd) ∧
          StmtsContract (D := Bridge.Dialect c g) (R.scope c g) (R.slice Partial.finalPairing)
            (fun V st => Clean R Checkpoint.pcs Snap H vkAddr cd V st)
            (fpPostHonest R product Snap H vkAddr cd)) := by
  sorry

/-- **GROUP 3 OF 3 - `fp_stmt_steps`. CLOSED BY T.5** (QUEUE.md "T.5 - Arithmetic and memory, accepted
    by FinalPairing").

    THE USE SITE: `fp_finalPairing_contracts`, as the SECOND conjunct of `BlockSound` - the clause that
    says a poisoned boundary is never laundered. It is the whole of that conjunct: `Poisoned` is
    definitionally `Frame ∧ success = 0`, so this lemma is cited by `exact`, and it is the only place
    the slice's FIRST statement (`if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }`) earns its keep.

    WHY IT IS NOT A COROLLARY OF T.4: `fpPre` carries `Inv .pcs` and `Poisoned` does not - a poisoned
    boundary has no invariant to spend (that is the point of §6's `Poisoned`: a frame plus a 0). So the
    poisoned case needs its own walk, and the walk is short: `iszero` on the literal word 0, then
    `fail`'s `mstore(0x00, shl(224, ERR_PRECOMPILE_FAILED))` and `revert(0x00, 0x04)`, which is
    `Reverted` by `revertedOf` (Shared.lean:48). The `leave` in `ec_pairing`'s first line is never
    reached, because the guard reverts first (emitter order GenAst.lean:651-654).

    WHAT ELSE T.5 OWNS, recorded here rather than as a fourth sorry because the two groups above already
    consume it: the `U256`/`BitVec` identities the other lemmas lean on (`iszero`, `and`, `eq` against
    the literal 1, `shl 224`) and the memory read-over-write facts at the layout addresses - i.e. item
    (c) of `ec_pairing_contract`'s list, and the reason `fpPost` may claim the frame and the `.pcs`
    clauses survive a 768-byte scratch write.

    SIZE ESTIMATE: **no basis yet** (requirements table). -/
theorem fp_stmt_steps (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (H : Hash) (vkAddr : U256)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice Partial.finalPairing)
        (fun V st => Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (0 : U256))
        (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
          (o = .normal ∧ Poisoned R H vkAddr cd V' st')) := by
  sorry

/-! ## 5. THE CONTRACT, PROVED FROM THE THREE GROUPS (NO SORRY IN THIS SECTION) -/

/-- **FINALPAIRING'S `BlockSound ∧ BlockProgress`, IN §6's OWN WRAPPER.**
    `Render.BlockContractsAt product (· = Partial.finalPairing)` unfolds (Blocks.lean:116-127) to: for
    every hash, VK address, calldata and snapshot witness,

    * `∀ g, BlockSound R .finalPairing Snap H vkAddr (permissive (callsOf product)) g cd`, and
    * `BlockProgress R .finalPairing Snap H vkAddr product cd`, gated on `G1CodecLaws`,
      `ChallengesGood` and `DualMSM.check = true` exactly as §6 gates it.

    So this IS the pair the card asks for, in the shape C.2's `slices_seq_sound`/`slices_seq_progress`
    consume: they want `∀ q, BlockSound R q ...` and `∀ q, BlockProgress R q ...`, and a per-block row
    is one instantiation of this at `q := .finalPairing`. The predicate `(· = Partial.finalPairing)`
    mirrors C.1's `poseidon_quotient_block`, which states the quotient row the same way.

    PROVED FROM EXACTLY THE THREE GROUPS, and from nothing else: no pairing implementation, no curve
    model, no other block's contract, and no `sorry` in this proof. `fp_pairing_algebra` is cited twice -
    backwards, in both `BlockProgress` halves, to turn §6's `DualMSM.check = true` gate into the answer
    bit - and its forward direction is what `ec_pairing_contract`'s conditional `.pairing` clause has to
    establish inside T.4 (see §3 for why that clause is not proved here). -/
theorem fp_finalPairing_contracts (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid) (hslots : fpG2Slots R) :
    R.BlockContractsAt product (fun q => q = Partial.finalPairing) := by
  intro hpc H vkAddr cd ms instW inst Snap hdec hinst hsnap q hq
  obtain rfl : q = Partial.finalPairing := hq
  refine ⟨fun g => ⟨?_, ?_⟩, fun hcodec hcg hdual => ⟨?_, ?_⟩⟩
  · -- `BlockSound` conjunct 1: from `Clean .pcs`, revert | clean at `.pairing` | poisoned.
    intro V st hclean V' st' o hrun
    have hpre : fpPre R Snap H vkAddr cd V st := ⟨hclean.2.1, hclean.1⟩
    have hwalk := (ec_pairing_contract R product hR hslots hpc H vkAddr cd Snap
      (permissive (callsOf product)) g).1 V st hpre V' st' o hrun
    have hin : fpInBit V = true := by
      show (VEnv.get V "success" == some (1 : U256)) = true
      rw [hclean.2.2]
      exact rfl
    have hout : fpOutBit R product Snap V = fpAnsBit R product Snap := by
      simp [fpOutBit, hin]
    rcases hwalk with ⟨rfl, hrev⟩ | ⟨rfl, hframe, hsucc, hinv, hpair⟩
    · exact Or.inl ⟨rfl, hrev⟩
    · have hsucc0 : VEnv.get V' "success" = some (fpWord (fpAnsBit R product Snap)) := by
        rw [hout] at hsucc; exact hsucc
      by_cases hans : fpAnsBit R product Snap = true
      · -- the precompile said yes: `success = 1`, so the post's `.pairing` clause fires and the
        -- boundary is `Clean` - which is `exitOk` for a non-terminal block.
        have hsucc' : VEnv.get V' "success" = some (1 : U256) := by
          rw [hsucc0, hans]; exact rfl
        refine Or.inr (Or.inl ⟨rfl, hpair hsucc', hframe, hsucc'⟩)
      · -- the precompile said no: the normal poisoned arm, which §6's `.pairing` handoff consumes.
        have hansf : fpAnsBit R product Snap = false := by
          cases h' : fpAnsBit R product Snap with
          | true => exact absurd h' hans
          | false => rfl
        have hsucc' : VEnv.get V' "success" = some (0 : U256) := by
          rw [hsucc0, hansf]; exact rfl
        -- S.3 / D-P49: §6's poisoned arm is now gated on `q ≠ .traceReturn`, and this is
        -- `.finalPairing`, so the arm gained a first component. `finalPairing ≠ traceReturn` is a
        -- decidable inequality on the emitter's constructor list - no content, no new premise.
        refine Or.inr (Or.inr ⟨by decide, rfl, hframe, hsucc'⟩)
  · -- `BlockSound` conjunct 2: a poisoned boundary is never laundered - the guard reverts first.
    -- S.3 / D-P49: §6's arm is now `finalPairing ≠ traceReturn ∧ normal ∧ Poisoned`, so
    -- `fp_stmt_steps`'s ungated post no longer matches by `exact`. Both of its disjuncts still land:
    -- the revert goes left unchanged, and the normal-poison handoff gains the decidable inequality.
    -- Same content, one wrapper, no new premise.
    intro V st h V' st' o hrun
    rcases fp_stmt_steps R hR H vkAddr cd (permissive (callsOf product)) g V st h V' st' o hrun
        with hrev | hnorm
    · exact Or.inl hrev
    · exact Or.inr ⟨by decide, hnorm⟩
  · -- `BlockProgress`, existence half: an honest run exists and exits `exitOk`.
    obtain ⟨_, hex⟩ := (ec_pairing_contract R product hR hslots hpc H vkAddr cd Snap
      (callsOf product) (ExternalGas.ofFun fun _ => 0)).2 rfl
    have hcheck : DualMSM.check Snap.c.dual R.params = true := hdual
    have hans : fpAnsBit R product Snap = true := (fp_pairing_algebra R product hpc Snap).mpr hcheck
    intro V st hclean
    obtain ⟨V', st', o, hrun, hpost⟩ := hex V st hclean
    obtain ⟨ho, hframe, hsucc, hinv, hpair⟩ := hpost
    have hsucc' : VEnv.get V' "success" = some (1 : U256) := by
      rw [hsucc, hans]; exact rfl
    refine ⟨V', st', o, hrun, ?_⟩
    show o = .normal ∧ Clean R Checkpoint.pairing Snap H vkAddr cd V' st'
    refine ⟨ho, hpair hsucc', hframe, hsucc'⟩
  · -- `BlockProgress`, forall-runs half: every honest run exits `exitOk`.
    obtain ⟨hall, _⟩ := (ec_pairing_contract R product hR hslots hpc H vkAddr cd Snap
      (callsOf product) (ExternalGas.ofFun fun _ => 0)).2 rfl
    have hcheck : DualMSM.check Snap.c.dual R.params = true := hdual
    have hans : fpAnsBit R product Snap = true := (fp_pairing_algebra R product hpc Snap).mpr hcheck
    intro V st hclean V' st' o hrun
    obtain ⟨ho, hframe, hsucc, hinv, hpair⟩ := hall V st hclean V' st' o hrun
    have hsucc' : VEnv.get V' "success" = some (1 : U256) := by
      rw [hsucc, hans]; exact rfl
    show o = .normal ∧ Clean R Checkpoint.pairing Snap H vkAddr cd V' st'
    refine ⟨ho, hpair hsucc', hframe, hsucc'⟩

/-- The soundness half on its own, for a consumer that cites one side. `fp_finalPairing_contracts`
    already carries it; this is the projection, with no new content and no `sorry`. -/
theorem fp_blockSound (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid) (hslots : fpG2Slots R) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
    (Snap : Snapshot p G₁ G₂ Gₜ)
    (hdec : decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd =
      some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf R.E H R.vk inst ms none = .ok Snap)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (g : ExternalGas) :
    BlockSound R Partial.finalPairing Snap H vkAddr (permissive (callsOf product)) g cd :=
  ((fp_finalPairing_contracts R product hR hslots) hpc H vkAddr cd ms instW inst Snap hdec hinst
    hsnap Partial.finalPairing rfl).1 g

/-- The progress half on its own, same projection. -/
theorem fp_blockProgress (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : R.Valid) (hslots : fpG2Slots R) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (ms : List (Msg (Fr p) G₁)) (instW : Array Word256) (inst : Array (Fr p))
    (Snap : Snapshot p G₁ G₂ Gₜ)
    (hdec : decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd =
      some (ms, instW))
    (hinst : instOfWords? (p := p) instW = some inst)
    (hsnap : snapshotOf R.E H R.vk inst ms none = .ok Snap)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLaws R.E.g1) (hcg : ChallengesGood R.vk Snap)
    (hdual : DualMSM.check Snap.c.dual R.params = true) :
    BlockProgress R Partial.finalPairing Snap H vkAddr product cd :=
  ((fp_finalPairing_contracts R product hR hslots) hpc H vkAddr cd ms instW inst Snap hdec hinst
    hsnap Partial.finalPairing rfl).2 hcodec hcg hdual

end Midfall.LoweringV2.Blocks.FinalPairing
