/-
  Midfall.Instances.VkKats

  The known-answer gates for `Generator/Vk.lean`, extracted from that file so the
  generator layer does not import `Instances/` (the import-confinement gate). The
  gates run on `Midfall.Instances.ExponentModel`; the namespace and declaration
  names are unchanged, so the emitted `#eval` gates still run through this module.
-/
import Midfall.Generator.Vk
import Midfall.Instances.ExponentModel

/-! # Known-answer tests

The model these gates run on is Midfall.Instances.ExponentModel (D-P1's runnable
AdmissiblePairing: three copies of the additive group of ZMod p, pairing =
multiplication of exponents). That import is a KAT-only dependency: this file
states no theorems, so nothing proved anywhere can acquire a dependence on the
exponent model, and scripts/checks.sh's axiom probe on the frozen statements is
unaffected. The model's own header (Instances/ExponentModel.lean:52-70) states
what it certifies and what it does not; these gates use it for exponent
arithmetic and for nothing else.

LANDMINE 1 (docs/REVIEW.md R-48): the shared LayoutKats.verifierLayoutFixture has
every PCS base at 0, so any gate that compares points passes vacuously on it.
This package therefore (a) builds memV, overriding the same seven bases Kzg.lean's
memF overrides for the same reason, (b) asserts pairwise distinctness
(fixturePointsDistinct_ok) BEFORE any comparison gate is trusted, and (c) leaves
the shared fixture alone. -/

namespace Midfall.Generator.VkKats

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Instances

local instance fact17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Reading a Fault-channel result as "did it panic at exactly this site". -/
def panickedAtSite {α : Type} (e : Except Fault α) (site : String) : Bool :=
  match e with
  | .error (Fault.panic s) => s == site
  | _ => false

def isFaultV {α : Type} (e : Except Fault α) : Bool :=
  match e with | .error _ => true | .ok _ => false

def isOkV {α : Type} (e : Except Fault α) : Bool :=
  match e with | .error _ => false | .ok _ => true

/-- The same probe on the Except String channel the layout validators use. -/
def isOkS {α : Type} (e : Except String α) : Bool :=
  match e with | .error _ => false | .ok _ => true

def orNat {α : Type} (e : Except Fault α) (d : α) : α :=
  match e with | .ok a => a | .error _ => d

def f17 (x : Fr 17) : Nat := x.val

/-- The Rust's panic-site prefix, spelled once. -/
def vkSite (n : Nat) : String :=
  "proofs/solidity-verifier/src/lowering/vk.rs:" ++ toString n

/-- The 48-byte little-endian Fp::to_repr of a small number, i.e. what
    g1_to_u256s / g2_to_u256s are handed by the reference. -/
def le48 (n : Nat) : List Nat := bytesToNats (natToBytesLE n 48)

/-- The port's stand-in for "the coordinates of this G1 point": exponent n, and a
    second coordinate that differs from the first so a swapped (x, y) or a swapped
    (hi, lo) is visible. Exponent 0 is the identity, the only point with no
    coordinates at all. -/
def g1ReprV : Exp 17 -> G1AffineRepr := fun P =>
  let n := P.toAdd.val
  if n == 0 then { coordinates := none, isIdentity := true }
  else { coordinates := some (le48 n, le48 (n + 1)), isIdentity := false }

/-- The G2 analogue: four distinct components, so the c0/c1 order inside each of
    x and y is observable and not only the x/y order. -/
def g2ReprV : Exp 17 -> G2AffineRepr := fun P =>
  let n := P.toAdd.val
  if n == 0 then
    { coordinates := none, isIdentity := true }
  else
    { coordinates := some ((le48 n, le48 (n + 1)), (le48 (n + 2), le48 (n + 3))),
      isIdentity := false }

def codecsV : VkPointCodecs (Exp 17) (Exp 17) :=
  { g1Repr := g1ReprV, g2Repr := g2ReprV }

/-- A REAL domain, built by the ported EvaluationDomain.new rather than
    hand-faked: fc17 has rootOfUnity = 3 of order 16, k = 2 and a degree-3
    constraint system, so n = 4 and omega is a primitive 4th root of 1 in
    ZMod 17. That it really is primitive is what fixtureDomain_ok checks - the
    hand-check hazard 3's finding says no lemma can replace yet. -/
def domV : EvaluationDomain (Fr 17) :=
  orNat (EvaluationDomain.new (F := Fr 17) fc17 3 2)
    { n := 0, k := 0, extendedK := 0, omega := 0, omegaInv := 0,
      extendedOmega := 0, extendedOmegaInv := 0, gCoset := 0, gCosetInv := 0,
      quotientPolyDegree := 0, ifftDivisor := 0, extendedIfftDivisor := 0,
      tEvaluations := #[], barycentricWeight := 0 }

/-- tau = 3, which is not in the domain: the four domain points are 1, omega,
    omega^2, omega^3 = 1, 13, 16, 4 and none of them is 3 (fixtureDomain_ok
    checks it). Chosen so that tau, minus tau and the four L_i(tau) are all
    distinct from each other AND from the commitment exponents below - which is
    what makes fixturePointsDistinct_ok true rather than a wish. -/
def tauV : Fr 17 := 3

/-- L_i(x) = (x^n - 1) / (n * omega^-i * (x - omega^i)), the closed form of the
    Lagrange basis over a multiplicative subgroup. Scaffolding for the fixture:
    it is how an honest g_lagrange is built, and the fact that it is honest is
    what srsTauCommitment_semantics_ok then checks. -/
def lagrangeAt (omega tau : Fr 17) (n i : Nat) : Fr 17 :=
  let x := omega ^ i
  (tau ^ n - 1) / ((n : Fr 17) * Inv.inv x * (tau - x))

/-- The honest Lagrange-basis SRS: g_lagrange[i] = L_i(tau) * G, over n = 4. -/
def gLagrangeV : List (Exp 17) :=
  (List.range domV.n).map fun i => ex (f17 (lagrangeAt domV.omega tauV domV.n i))

/-- The honest G2 side: s_g2 = tau * G2. -/
def sG2V : Exp 17 := gsmul tauV (expGen (p := 17))

/-- The commitment points, all distinct and none the identity, so a gate that
    compares them can actually fail (landmine 1). -/
def fixedV : Array (Exp 17) := #[ex 2, ex 6]
def permV : Array (Exp 17) := #[ex 7, ex 9, ex 11]

def vkCurveV : VerifyingKey (Fr 17) (Exp 17) :=
  { domain := domV
    fixedCommitments := fixedV
    permutation := { commitments := permV }
    cs := ConstraintSystem.default (F := Fr 17)
    csDegree := 3
    transcriptRepr := 7 }

def paramsV : ParamsKZG (Exp 17) (Exp 17) :=
  { gLagrange := gLagrangeV, g2 := expGen (p := 17), sG2 := sG2V }

def accV : Midfall.Generator.AccumulatorEncoding :=
  { offset := 4, numLimbs := 7, numLimbBits := 56,
    kind := Midfall.Generator.AccumulatorEncodingKind.pointAndScalar }

/-- rust: MOD:37-45 as a value: the six fields, filled. -/
def inputsV : VerifierBuildInputs 17 (Exp 17) (Exp 17) :=
  { params := paramsV,
    vk := vkCurveV,
    numInstances := 3,
    numCommittedInstances := 1,
    accEncoding := some accV,
    meta_ := Midfall.Generator.EncodingKats.metaFixture }

/-- The same inputs with no accumulator: VK:119-131's unwrap_or_default arm. -/
def inputsNoAcc : VerifierBuildInputs 17 (Exp 17) (Exp 17) :=
  { inputsV with accEncoding := none }

/-- The memory layout the stub planner returns. Built from the shared fixture
    with SEVEN bases overridden - the same seven Kzg.lean:1872-1880 overrides, for
    the reason R-48 records: with every PCS base at 0 the commitment pointers
    coincide and a comparison gate cannot fail. -/
def memV : VerifierMemoryLayout :=
  { Midfall.Generator.EncodingKats.memFixture with
    quotientLimbCommsMptrBase := ptrMemory (valueFromNat 0x7000)
    fComMptr := ptrMemory (valueFromNat 0x9000)
    piMptr := ptrMemory (valueFromNat 0x9020)
    pcsQEvalSourceTableMptr := 0x8000
    pcsQComTraceScratchMptr := 0x8100
    pcsFinalMsmScratchMptr := 0x8200
    pcsPairingScratchMptr := 0x9200 }

/-- The stub for the unported VerifierMemoryLayout::new (MEM:591-973). A STUB, and
    it says so: it returns memV regardless, except that it copies the two config
    fields memory_layout_for is supposed to fill into fields the gates can read
    back. That is what makes memoryLayoutFor_config_ok a gate and not a tautology:
    a port that forgot VK:557-559 leaves both at the default zero. -/
def newLayoutV : ConstraintSystemMeta -> Halo2VerifyingKey -> Ptr ->
    VerifierMemoryLayoutConfig -> VerifierMemoryLayout :=
  fun _ _ vkMptr cfg =>
    { memV with
      vkMptr := vkMptr
      transcriptMptr := cfg.transcriptWords
      verifierReturnMptr := cfg.numInstances }

/-- A quotient build with three constants and forty program bytes, i.e. two
    program words, so the two reservation sizes are non-degenerate and distinct. -/
def buildV : VkQuotientBuild :=
  { bytes := ByteArray.mk ((List.range 40).map Nat.toUInt8).toArray
    consts := [101, 202, 303] }

/-- The three quotient.rs stubs (QRS:165-181, QRS:425-430, QRS:2101-2110).
    Deterministic, which is exactly the property VK:456-463 asserts of the real
    ones; the two "changed after materialisation" gates break that on purpose to
    show the asserts can fire. -/
def envV : VkBuildEnv Nat :=
  { newVerifierMemoryLayout := newLayoutV
    compactQuotientProgramFor := fun _ _ => Except.ok buildV
    quotientProgramPlan := fun _ _ => Except.ok 0
    buildQuotientProgramItems := fun _ => Except.ok buildV }

/-- The render-side VK the meta/data path is built against: Encoding.lean's own
    fixture, so Data.new's internal asserts hold exactly as Encoding.lean already
    pins them. -/
def renderVkV : Halo2VerifyingKey := Midfall.Generator.EncodingKats.vkFixture

/-- The empty Data used as a loud fallback by one gate below. -/
def dataEmptyStub : Data := Midfall.Generator.EncodingKats.dataEmpty


/-! ## Fixture sanity -/

/-- THE DOMAIN AND THE SRS ARE HONEST, which is the hand-check hazard 3's finding
    says no lemma can replace yet. Five things: omega has order EXACTLY 4 (so it is
    a primitive 4th root - precisely the hypothesis R-47 says the tree does not
    carry); the four domain points are distinct; tau is off the domain; the
    Lagrange basis sums to 1 (the constant-1 polynomial, which is what VK:141-144
    says the sum of g_lagrange must be); and the basis reproduces X at tau. Rules
    out a fixture whose SRS was not honestly generated, which would make every
    assert gate below vacuous in the wrong direction.
    PERTURBATION RUN: setting tauV to 1 (a domain point) reddens the third and
    fourth conjuncts, because a Lagrange basis evaluated AT a domain point is a
    delta function that still sums to 1 but reproduces 1 and not tau. Replacing
    omega ^ i by omega ^ (i + 1) in lagrangeAt reddens the fifth conjunct and
    srsTauCommitment_semantics_ok. Replacing fc17's rootOfUnity with 2 reddens the
    first conjunct. -/
def fixtureDomain_ok : Bool :=
  f17 domV.omega == 13 && f17 domV.omegaInv == 4 && domV.n == 4 && domV.k == 2
    && f17 (domV.omega ^ 4) == 1 && f17 (domV.omega ^ 1) != 1
    && f17 (domV.omega ^ 2) != 1 && f17 (domV.omega ^ 3) != 1
    && ! [1, 13, 16, 4].contains (f17 tauV)
    && ((List.range 4).map (fun i => f17 (domV.omega ^ i))).eraseDups.length == 4
    && f17 ((List.range 4).foldl
        (fun acc i => acc + lagrangeAt domV.omega tauV 4 i) 0) == 1
    && f17 ((List.range 4).foldl (fun acc i =>
          acc + domV.omega ^ i * lagrangeAt domV.omega tauV 4 i) 0) == f17 tauV

/-- LANDMINE 1'S DISTINCTNESS ASSERTION, made before any comparison gate below is
    trusted. The fixture's group elements - four g_lagrange points, the G1 base,
    s_g2, minus s_g2, and the five commitment points - must be pairwise distinct as
    points, as exponents, and as encoded word quadruples. Without this,
    generateBaseVk_comms_ok and generateBaseVk_g1g2Slots_ok would be comparing a
    value against itself.
    PERTURBATION RUN: setting permV to #[ex 2, ex 3, ex 2] (repeating two fixed
    commitments) reddens this gate and nothing else, which is the point: the
    comparison gates stay green on a degenerate fixture and this one does not. -/
def fixturePointsDistinct_ok : Bool :=
  let pts : List (Exp 17) :=
    gLagrangeV ++ [expGen (p := 17), sG2V, Inv.inv sG2V] ++ fixedV.toList ++ permV.toList
  pts.length == pts.eraseDups.length
    && (pts.map (fun q => q.toAdd.val)).eraseDups.length == pts.length
    && (match (pts.mapM fun q => g1ToU256s (g1ReprV q)) with
        | .ok ws => (ws.map (fun w => w.map (fun x => x.toNat))).eraseDups.length == ws.length
        | .error _ => false)

/-! ## The VK header schema block (LM:396-665) -/

/-- rust: LM:824-831, the reference's OWN test of the slot words and the header
    width, ported: VkDigest 0, G1Base 11, G2Base 15, NegSG2Base 23, header_words
    31, and the field widths summing to the header width. The seven scalar slots
    between them are ones the reference does not pin and this does.
    PERTURBATION RUN: changing VkHeaderSlot.word's omegaInv arm from 5 to 6
    reddens this gate and generateBaseVk_header_ok. -/
def vkHeaderSlot_word_ok : Bool :=
  VkHeaderSlot.word .vkDigest == 0 && VkHeaderSlot.word .numInstances == 1
    && VkHeaderSlot.word .k == 2 && VkHeaderSlot.word .nInv == 3
    && VkHeaderSlot.word .omega == 4 && VkHeaderSlot.word .omegaInv == 5
    && VkHeaderSlot.word .omegaInvToL == 6
    && VkHeaderSlot.word .hasAccumulator == 7
    && VkHeaderSlot.word .accOffset == 8 && VkHeaderSlot.word .numAccLimbs == 9
    && VkHeaderSlot.word .numAccLimbBits == 10
    && VkHeaderSlot.word .g1Base == 11 && VkHeaderSlot.word .g2Base == 15
    && VkHeaderSlot.word .negSG2Base == 23
    && VkHeaderLayout.headerWords == 31
    && (VkHeaderLayout.fields.map (fun f => f.widthWords)).foldl (· + ·) 0 == 31
    && VkHeaderLayout.fields.length == 14

/-- The closed match in VkHeaderLayout.field agrees with the table it replaces, for
    all fourteen slots, on all three fields. This is the gate that keeps the
    "LM:556 is unrepresentable" claim honest: add a slot to the enum and forget the
    table, and the match still compiles - only this says.
    PERTURBATION RUN: renaming the table's "n_inv" to "ninv" reddens this gate
    alone; changing the match's nInv width to 2 reddens this gate and
    vkHeaderSlot_word_ok. -/
def vkHeaderField_agreesWithTable_ok : Bool :=
  let slots : List VkHeaderSlot := [.vkDigest, .numInstances, .k, .nInv, .omega,
    .omegaInv, .omegaInvToL, .hasAccumulator, .accOffset, .numAccLimbs,
    .numAccLimbBits, .g1Base, .g2Base, .negSG2Base]
  slots.length == 14
    && slots.all (fun s =>
      match (VkHeaderLayout.fields.find? (fun f => f.slot == s)) with
      | some f => VkHeaderLayout.field s == f
      | none => false)

/-- A full header build: thirty-one words in the schema's order, each carrying the
    name the caller passed and the value it passed. This is the header half of
    hazard 7 - the ORDER, not the count: a builder that wrote G1_BASE into the
    G2_BASE slot, or emitted the scalars in another order, keeps the count at 31
    and is caught only here.
    PERTURBATION RUN: swapping the two g2 calls' slots reddens this gate and
    generateBaseVk_g1g2Slots_ok; writing numAccLimbBits twice reddens it with the
    overlap error. -/
def vkHeaderBuilder_fullOk_ok : Bool :=
  let v (n : Nat) : Word256 := BitVec.ofNat 256 n
  let bs : List (VkHeaderSlot × String) := [(.vkDigest, "vk_digest"),
    (.numInstances, "num_instances"), (.k, "k"), (.nInv, "n_inv"), (.omega, "omega"),
    (.omegaInv, "omega_inv"), (.omegaInvToL, "omega_inv_to_l"),
    (.hasAccumulator, "has_accumulator"), (.accOffset, "acc_offset"),
    (.numAccLimbs, "num_acc_limbs"), (.numAccLimbBits, "num_acc_limb_bits")]
  match bs.foldlM (fun (h : VkHeaderBuilder) (s, n) => h.scalar s n (v 7))
      VkHeaderLayout.builder with
  | .error _ => false
  | .ok h1 =>
    match h1.g1 .g1Base ["g1_x_hi", "g1_x_lo", "g1_y_hi", "g1_y_lo"]
        ((List.range 4).map (fun i => v (100 + i))) with
    | .error _ => false
    | .ok h2 =>
      match h2.g2 .g2Base ((List.range 8).map (fun i => "g2_" ++ toString i))
          ((List.range 8).map (fun i => v (200 + i))) with
      | .error _ => false
      | .ok h3 =>
        match h3.g2 .negSG2Base ((List.range 8).map (fun i => "neg_" ++ toString i))
            ((List.range 8).map (fun i => v (300 + i))) with
        | .error _ => false
        | .ok h4 =>
          match h4.finish with
          | .error _ => false
          | .ok cs =>
            cs.length == 31
              && cs.getD 0 ("", 0) == ("vk_digest", v 7)
              && cs.getD 6 ("", 0) == ("omega_inv_to_l", v 7)
              && cs.getD 10 ("", 0) == ("num_acc_limb_bits", v 7)
              && cs.getD 11 ("", 0) == ("g1_x_hi", v 100)
              && cs.getD 14 ("", 0) == ("g1_y_lo", v 103)
              && cs.getD 15 ("", 0) == ("g2_0", v 200)
              && cs.getD 22 ("", 0) == ("g2_7", v 207)
              && cs.getD 23 ("", 0) == ("neg_0", v 300)
              && cs.getD 30 ("", 0) == ("neg_7", v 307)

/-- rust: LM:837-846, the reference's own duplicate-slot test, ported: writing
    VkDigest twice fails with the OVERLAP message naming the word index.
    PERTURBATION RUN: making insert overwrite instead of rejecting reddens this
    gate and leaves vkHeaderBuilder_fullOk_ok green, which is the pair that shows
    the check is load-bearing. -/
def vkHeaderBuilder_duplicateErr_ok : Bool :=
  match (VkHeaderLayout.builder).scalar .vkDigest "vk_digest" 1
      >>= (fun b => b.scalar .vkDigest "vk_digest" 2) with
  | .error m => m == "VK header field vk_digest overlaps already-written word 0"
  | .ok _ => false

/-- rust: LM:848-851 (the too-wide insert) plus LM:594's word-count arm, both
    ported and both pinned: the descriptor/caller width mismatch and the
    values-length mismatch are DIFFERENT messages, so a port that collapses them
    passes a count-only check and fails this one. -/
def vkHeaderBuilder_widthErr_ok : Bool :=
  let b := VkHeaderLayout.builder
  (match b.insert .g1Base 8 [] with
    | .error m => m == "VK header field G1_BASE width mismatch: descriptor=4 caller=8"
    | .ok _ => false)
    && (match b.g1 .g1Base ["a", "b"] [1, 2] with
        | .error m => m == "VK header field G1_BASE expected 4 word(s), got 2"
        | .ok _ => false)

/-- LM:603-609's overflow arm. Unreachable through the typed slots - every slot
    fits a 31-word header - so it is exercised by calling insert directly on a
    truncated builder. The range in the message is start..end in DECIMAL, matching
    LM:605's format string, which is itself worth a note: every other address in
    these messages is hex (Layout.lean's hashHex), and this one is not.
    PERTURBATION RUN: rendering the range with hashHex reddens this gate. -/
def vkHeaderBuilder_overflowErr_ok : Bool :=
  let b : VkHeaderBuilder := { words := List.replicate 12 none }
  match b.insert .g2Base 8 ((List.range 8).map (fun i => ("w" ++ toString i, 0))) with
  | .error m => m == "VK header field G2_BASE overflows header: range 15..23, header=12"
  | .ok _ => false

/-- LM:656-664's finish error: the empty builder reports word 0, and a builder whose
    only unset word is number 3 reports 3. The second arm is the one that pins the
    short-circuit - a port that collected every missing word and reported the last
    would say 3 as well, so what it really pins is that the fold reports the FIRST
    missing word and stops; the word-index-versus-unwritten-index distinction is not
    observable at all (see the note at VkHeaderBuilder.finish and perturbation P14). -/
def vkHeaderBuilder_finishMissingErr_ok : Bool :=
  (match (VkHeaderLayout.builder).finish with
    | .error m => m == "VK header word 0 was not written"
    | .ok _ => false)
    && (match ({ words := [some ("a", 1), some ("b", 2), some ("c", 3), none] }
        : VkHeaderBuilder).finish with
        | .error m => m == "VK header word 3 was not written"
        | .ok _ => false)

/-! ## The tau binding (VK:29-62) -/

/-- HAZARD 2. The mutating accumulator's output, pinned four ways: the first eight
    entries against hand-computed powers, the two degenerate lengths, and the
    equivalence with omega ^ i that the port deliberately does NOT rely on.
    PERTURBATION RUN: yielding the accumulator AFTER the multiply (moving VK:56's
    current below VK:57) reddens the first conjunct and
    srsTauCommitment_semantics_ok. Replacing the fold with omega ^ i leaves this
    gate green - which is exactly what the fifth conjunct is for: it makes the
    substitution safe rather than lucky. -/
def omegaPowers_accumulatorEquivalence_ok : Bool :=
  let w := domV.omega
  let ps := omegaPowers w 8
  (ps.map f17 == [1, 13, 16, 4, 1, 13, 16, 4])
    && omegaPowers w 0 == []
    && (omegaPowers w 1).map f17 == [1]
    && ps.length == 8
    && ps.zipIdx.all (fun (x, i) => f17 x == f17 (w ^ i))
    && (omegaPowers 3 5).map f17 == [1, 3, 9, 10, 13]

/-- HAZARD 1'S GATE. The semantics of the multi_exp, at the sizes the port is
    allowed to run (4 and 8, never 2^20). Four conjuncts: (a) on the honest
    fixture the result is tau * G, which is the whole point of the function and
    the content of the Phase 4a lemma, checked here on one concrete domain rather
    than proved; (b) it equals a hand-written fold of omega^i * g_i computed
    WITHOUT omegaPowers, so the two cannot share a bug; (c) the empty SRS gives the
    identity; (d) doubling the basis doubles the commitment, the first thing a
    bucket-decomposition shortcut would get wrong.
    PERTURBATION RUN: P01 (yield the accumulator after the multiply, i.e. start
    the list at omega instead of 1) reddens this gate plus sixteen others. P33
    (same shift written the other way) does too. Replacing omega^i with omega^(i+1)
    reddens (a). Dropping the fold and returning the last term reddens (a), (b), (d).
    ONE CLAIM IN AN EARLIER DRAFT OF THIS COMMENT WAS FALSE AND IS CORRECTED HERE:
    it said that swapping the zip so the SCALARS become the BASES - reading
    multi_exp's argument order backwards - would redden (a) and (b). It does not,
    because it CANNOT be written: gsmul takes a scalar and a point, so the two lists
    are different types and no transposition of the zip is well-typed. The argument
    order of VK:61 is therefore carried by the Lean types and not by this gate, and
    a perturbation attempt that only renames the pair pattern (g, s) / (s, g) is a
    no-op - which is what actually happened when it was run (P02, nothing reddened). -/
def srsTauCommitment_semantics_ok : Bool :=
  let w := domV.omega
  let tauG1 := srsTauCommitment gLagrangeV w
  expOf tauG1 == f17 tauV
    && expOf ((List.range 4).foldl
        (fun acc i => acc * gsmul (w ^ i) (gLagrangeV.getD i 1)) 1) == expOf tauG1
    && expOf (srsTauCommitment [] w) == 0
    && expOf (srsTauCommitment (gLagrangeV ++ gLagrangeV) w) == f17 (tauV * 2)

/-- HAZARD 3'S GATE, and the stand-in for the lemma that cannot be stated yet.
    True on the honest fixture; FALSE when s_g2 is the commitment of a different
    tau, which is exactly the substituted-SRS case VK:195-198 says the assert
    exists to catch; FALSE when the basis is tampered with. The false arms are what
    make this gate non-vacuous: a srsTauIsConsistent that returned true
    unconditionally would pass a one-conjunct version of this gate.
    PERTURBATION RUN: returning true unconditionally reddens the second and third
    conjuncts. Swapping the pairing's two arguments so the check becomes
    e(tau*G1, s_g2) = e(G1, G2) reddens the first conjunct, because that equation
    says tau = 1. -/
def srsTauIsConsistent_honestSrs_ok : Bool :=
  srsTauIsConsistent gLagrangeV domV.omega sG2V
    && ! srsTauIsConsistent gLagrangeV domV.omega (ex 6)
    && ! srsTauIsConsistent (gLagrangeV ++ [ex 1]) domV.omega sG2V

/-! ## The SRS fingerprint (VK:73-92) -/

/-- HAZARD 4: the EXACT preimage bytes, not just the digest, because the digest
    feeds BUILD_ID and a deployed artifact carries it. The layout is
    30 + 8 + 256 + 256 + 128 = 678 bytes: the ASCII tag, then n as EIGHT
    big-endian bytes, then the eight G2 words of g2, then the eight G2 words of
    s_g2, then the four G1 words of [tau]G1, every word 32 big-endian bytes. Every
    segment is pinned at its own offset, so a stride change, a dropped segment, or
    a swapped pair of segments all show up.
    PERTURBATION RUN: writing n as 32 bytes (the natural mistake, since every other
    segment is 32) reddens the length conjunct and the n conjunct; dropping the g2
    segment reddens the length and the offset-38 conjunct; hashing the words
    little-endian reddens the word conjuncts; hashing the preimage twice reddens the
    last conjunct. -/
def srsFingerprint_preimage_ok : Bool :=
  match srsFingerprintPreimage codecsV inputsV
      (srsTauCommitment gLagrangeV domV.omega) with
  | .error _ => false
  | .ok pre =>
    let bs := bytesToNats pre
    let byteAt (k : Nat) : Nat := bs.getD k 255
    -- The value of word j of the segment starting at byte off. Every word here is
    -- a small number, so it lives in the segment's last byte; padsOk is what stops a
    -- wrong-endian or wrong-stride encoding from passing on the value byte alone.
    let wordVals (off nwords : Nat) : List Nat :=
      (List.range nwords).map (fun j => byteAt (off + j * 32 + 31))
    let padsOk (off nwords : Nat) : Bool :=
      ((List.range (nwords * 32)).all (fun i => i % 32 == 31 || byteAt (off + i) == 0))
    bs.length == 678
      && bs.take 30 == ("halo2-solidity-verifier-srs-v1".toList.map (fun c => c.toNat))
      && (bs.drop 30).take 8 == [0, 0, 0, 0, 0, 0, 0, 4]
      && wordVals 38 8 == [0, 1, 0, 2, 0, 3, 0, 4] && padsOk 38 8
      && wordVals 294 8 == [0, 3, 0, 4, 0, 5, 0, 6] && padsOk 294 8
      && wordVals 550 4 == [0, 3, 0, 4] && padsOk 550 4
      && (match srsFingerprint codecsV inputsV with
          | .error _ => false
          | .ok h => h == keccak256 pre)
      && (match srsFingerprint codecsV inputsV with
          | .error _ => false
          | .ok h => h != keccak256 (bytesFromNats (bs ++ [0])))

/-- HAZARD 4's cross-check of the field ORDER the doc comment names (n, G2 base,
    s_g2, [tau]G1). Two things a count check cannot see: that changing tau moves
    the s_g2 segment and nothing before it, and that the digests differ, so a
    substituted SRS would carry a different BUILD_ID.
    The 32-byte slice is NOT enough to see the change - the first word of a G2
    encoding is x.c0_hi, which is zero for every small exponent - so the second
    conjunct compares the whole 256-byte segment. That was found by running it, not
    by reasoning: the first version of this gate compared 32 bytes and passed
    without noticing.
    PERTURBATION RUN: emitting [tau]G1 before s_g2 reddens the first conjunct (the
    bytes at offset 294 would then be the G1 quadruple and everything after
    shifts). Swapping the g2 and s_g2 segments reddens the first conjunct too,
    because g2 is exponent 1 and s_g2 is exponent 3. -/
def srsFingerprint_fieldOrder_ok : Bool :=
  let honest := match srsFingerprintPreimage codecsV inputsV
      (srsTauCommitment gLagrangeV domV.omega) with
    | .ok b => b
    | .error _ => Bytes.empty
  let paramsOther : ParamsKZG (Exp 17) (Exp 17) := { paramsV with sG2 := ex 6 }
  let other : VerifierBuildInputs 17 (Exp 17) (Exp 17) :=
    { inputsV with params := paramsOther }
  match srsFingerprintPreimage codecsV other (srsTauCommitment gLagrangeV domV.omega) with
  | .error _ => false
  | .ok changed =>
    ((bytesToNats honest).take 294) == ((bytesToNats changed).take 294)
      && ((bytesToNats honest).drop 294).take 256
          != ((bytesToNats changed).drop 294).take 256
      && (match srsFingerprint codecsV inputsV, srsFingerprint codecsV other with
          | .ok h1, .ok h2 => h1 != h2
          | _, _ => false)


/-! ## generate_base_vk (VK:94-299) -/

/-- The header half of hazard 7: the thirty-one constants the reference emits,
    pinned by NAME and by VALUE at every slot, in order. The values are the
    fixture's own: transcript_repr 7, num_instances 3, k 2, n_inv = 4^-1 = 13,
    omega 13, omega_inv 4, omega_inv^|rotation_last| = 4^10 = 16 (omega_inv has
    order 4, so the tenth power is the second), and the accumulator quadruple
    1 / 4 / 7 / 56. Then the three point fields.
    PERTURBATION RUN: putting omega_inv (4) where n_inv belongs reddens this gate.
    So does reading num_main_evals where the reference reads num_instances, and so
    does dropping the Int.natAbs at VK:116 (l := 0 instead of 10).
    ONE PERTURBATION THAT DID NOT REDDEN, stated because the fixture is the reason:
    putting OMEGA where n_inv belongs reddens nothing, because at k = 2 over Fr 17
    n_inv = (2^2)^-1 = 4^-1 = 13 and omega = 13 are the same number. That is a
    property of the chosen domain, not of the port - and it is the R-30 shape (a
    fixture that collapses two distinct slots onto one value), so this gate cannot
    distinguish those two slots and no claim is made that it does. -/
def generateBaseVk_header_ok : Bool :=
  match generateBaseVk codecsV inputsV with
  | .error _ => false
  | .ok vk =>
    let cs := vk.constants
    cs.length == 31
      && cs.map (fun c => c.1) == ["vk_digest", "num_instances", "k", "n_inv",
          "omega", "omega_inv", "omega_inv_to_l", "has_accumulator", "acc_offset",
          "num_acc_limbs", "num_acc_limb_bits", "g1_x_hi", "g1_x_lo", "g1_y_hi",
          "g1_y_lo", "g2_x_c0_hi", "g2_x_c0_lo", "g2_x_c1_hi", "g2_x_c1_lo",
          "g2_y_c0_hi", "g2_y_c0_lo", "g2_y_c1_hi", "g2_y_c1_lo",
          "neg_s_g2_x_c0_hi", "neg_s_g2_x_c0_lo", "neg_s_g2_x_c1_hi",
          "neg_s_g2_x_c1_lo", "neg_s_g2_y_c0_hi", "neg_s_g2_y_c0_lo",
          "neg_s_g2_y_c1_hi", "neg_s_g2_y_c1_lo"]
      && cs.map (fun c => c.2.toNat) ==
          [7, 3, 2, 13, 13, 4, 16, 1, 4, 7, 56,
           0, 1, 0, 2,
           0, 1, 0, 2, 0, 3, 0, 4,
           0, 14, 0, 15, 0, 16, 0, 17]

/-- The three point slots at their BYTE offsets, which is what hazard 7 asks for
    beyond a count: G1_BASE at word 11 = byte 352, G2_BASE at word 15 = byte 480,
    NEG_S_G2_BASE at word 23 = byte 736. The negation is checked to be a REAL
    negation - s_g2 is exponent 3, minus s_g2 is exponent 14, and the eight words
    differ in the four places a missing minus sign would leave equal.
    PERTURBATION RUN: dropping the inverse at VK:159 reddens the last conjunct and
    nothing else in the file, because every other use of s_g2 goes through the
    un-negated value. Writing the G2 words in (c1, c0) order reddens the
    byte-offset conjuncts. -/
def generateBaseVk_g1g2Slots_ok : Bool :=
  match generateBaseVk codecsV inputsV with
  | .error _ => false
  | .ok vk =>
    let payload := vk.bytes
    let wordAt (byteOff : Nat) : Nat :=
      bytesToNatBE ((bytesTake payload byteOff 32).getD Bytes.empty)
    wordAt 352 == 0 && wordAt 384 == 1 && wordAt 416 == 0 && wordAt 448 == 2
      && wordAt 480 == 0 && wordAt 512 == 1 && wordAt 736 == 0 && wordAt 768 == 14
      && (vk.constants.map (fun c => c.2.toNat)).getD 23 999 == 0
      && (vk.constants.map (fun c => c.2.toNat)).getD 24 999 == 14
      && expOf sG2V == 3 && expOf (Inv.inv sG2V) == 14

/-- The three SRS asserts, each at its own site, each broken independently. This is
    the gate that says the controls the audit calls H-1 actually fire: a bad
    g_lagrange sum (VK:151), a non-canonical G2 base (VK:180), and an s_g2 that does
    not correspond to the tau behind g_lagrange (VK:189).
    PERTURBATION RUN: this gate is the evidence for the three sites. Deleting any
    one unless from generateBaseVk reddens exactly the conjunct that expects that
    panic and leaves the other two green, which is what makes the three sites
    separately observable rather than one lump. -/
def generateBaseVk_srsAsserts_ok : Bool :=
  panickedAtSite (generateBaseVk codecsV
    { inputsV with params := { paramsV with gLagrange := gLagrangeV.drop 1 } })
      (vkSite 151)
    && panickedAtSite (generateBaseVk codecsV
      { inputsV with params := { paramsV with g2 := ex 2 } }) (vkSite 180)
    && panickedAtSite (generateBaseVk codecsV
      { inputsV with params := { paramsV with sG2 := ex 6 } }) (vkSite 189)
    && isOkV (generateBaseVk codecsV inputsV)

/-- The commitment vectors: two fixed and three permutation commitments, each four
    words, each from a DISTINCT point (landmine 1), in source order, and the
    constructor reservation sized from them: 31*32 + 5*128 bytes plus the 1-byte
    runtime prefix. Also pins that the base VK carries NO quotient section, which is
    what makes payload_layout's constants-minus-quotient-words arithmetic yield the
    header width and not something else.
    PERTURBATION RUN: emitting the permutation commitments from the fixed vector
    (the classic copy-paste) reddens the word comparison; using g1Bytes where the
    reference uses WORD_BYTES at VK:281 reddens the length conjunct. -/
def generateBaseVk_comms_ok : Bool :=
  match generateBaseVk codecsV inputsV with
  | .error _ => false
  | .ok vk =>
    vk.fixedComms.length == 2 && vk.permutationComms.length == 3
      && vk.fixedComms.map (fun w => [w.xHi.toNat, w.xLo.toNat, w.yHi.toNat, w.yLo.toNat])
          == [[0, 2, 0, 3], [0, 6, 0, 7]]
      && vk.permutationComms.map (fun w => [w.xHi.toNat, w.xLo.toNat, w.yHi.toNat, w.yLo.toNat])
          == [[0, 7, 0, 8], [0, 9, 0, 10], [0, 11, 0, 12]]
      && vk.len == 31 * 32 + 5 * 128
      && vk.constructorPayloadMptr == vkConstructorPayloadStart
      && vk.quotientConstOffsetWords == none && vk.quotientConstWords == 0
      && vk.quotientProgramOffsetWords == none && vk.quotientProgramWords == 0
      && vk.quotientConstLabels == [] && vk.quotientConstHeaders == []
      && (VkConstructorMemoryLayout.new (vk.len + vkRuntimePrefixLen)).validate == .ok ()

/-- VK:119-131, both arms of the accumulator option: is_some() as usize for the
    flag and unwrap_or_default() for the three values. The no-accumulator arm is the
    one a port that defaults to 1/1/1 gets wrong, and it is also the arm the deployed
    Moonlight build does not take, so both are pinned.
    PERTURBATION RUN: reading offset into num_acc_limbs reddens the second
    conjunct; using 1 for has_accumulator when absent reddens the first. -/
def generateBaseVk_accEncoding_ok : Bool :=
  match generateBaseVk codecsV inputsNoAcc, generateBaseVk codecsV inputsV with
  | .ok vk0, .ok vk1 =>
    let w0 := vk0.constants.map (fun c => c.2.toNat)
    let w1 := vk1.constants.map (fun c => c.2.toNat)
    [w0.getD 7 999, w0.getD 8 999, w0.getD 9 999, w0.getD 10 999] == [0, 0, 0, 0]
      && [w1.getD 7 999, w1.getD 8 999, w1.getD 9 999, w1.getD 10 999] == [1, 4, 7, 56]
  | _, _ => false

/-- VK:115-118: omega_inv_to_l is omega_inv raised to the ABSOLUTE value of
    rotation_last, which for the fixture meta is -10, so 4^10 mod 17 = 16. The
    signedness is the point: a port that used the signed rotation, or that forgot
    the abs, gets a different word, and the difference is invisible to any length or
    count check.
    PERTURBATION RUN: using the signed exponent reddens this gate (powVartime on a
    negative is not what the reference computes). So does using omega instead of
    omega_inv: 13^10 = 1, not 16. -/
def generateBaseVk_omegaInvToL_ok : Bool :=
  inputsV.meta_.rotationLast == -10
    && f17 (powVartime domV.omegaInv 10) == 16
    && f17 (powVartime domV.omegaInv 0) == 1
    && f17 (powVartime domV.omegaInv 1) == 4
    && match generateBaseVk codecsV inputsV with
       | .ok vk => (vk.constants.getD 6 ("", 0)).2.toNat == 16
       | .error _ => false

/-! ## generate_vk_direct (VK:301-357) -/

/-- The direct lowering: the constant table grows by the table words, the
    quotient-program section is reserved at ZERO words but still gets an offset, the
    labels are one per word, and the headers are keyed by the index in the WHOLE
    table after enumerate-then-filter. Also the assert at VK:343 that the typed
    layout preserves the emitted byte length.
    PERTURBATION RUN: filtering before enumerating, so the header indices count only
    the headed words, reddens the headers conjunct; setting quotient_program_words
    to 1 instead of 0 reddens the length conjunct. -/
def generateVkDirect_table_ok : Bool :=
  let words : List VkTableWord :=
    [ { value := 11, label := "run_a[0]", headers := ["hdr 1", "hdr 2"] },
      { value := 12, label := "run_a[1]", headers := [] },
      { value := 13, label := "pool[0]", headers := ["hdr 3"] } ]
  match generateVkDirect codecsV inputsV words with
  | .error _ => false
  | .ok vk =>
    vk.constants.length == 34
      && vk.constants.getD 31 ("", 0) == ("quotient_const", 11)
      && vk.constants.getD 33 ("", 0) == ("quotient_const", 13)
      && vk.quotientConstWords == 3
      && vk.quotientProgramWords == 0
      && vk.quotientConstOffsetWords == some 31
      && vk.quotientProgramOffsetWords == some 34
      && vk.quotientConstLabels == ["run_a[0]", "run_a[1]", "pool[0]"]
      && vk.quotientConstHeaders == [(0, ["hdr 1", "hdr 2"]), (2, ["hdr 3"])]
      && vk.len == 34 * 32 + 5 * 128
      && isOkS (vk.validatePayloadLayout)

/-- The empty-table arm: a direct program with no words still gets both offsets,
    the two quotient sections collapse onto the cursor, and the byte length is still
    preserved. A port that skipped the layout call when the table was empty would
    leave none in the offset fields and fail here. -/
def generateVkDirect_empty_ok : Bool :=
  match generateVkDirect codecsV inputsV [] with
  | .error _ => false
  | .ok vk =>
    vk.constants.length == 31 && vk.quotientConstWords == 0
      && vk.quotientConstOffsetWords == some 31
      && vk.quotientProgramOffsetWords == some 31
      && vk.quotientConstLabels == [] && vk.quotientConstHeaders == []
      && isOkS (vk.validatePayloadLayout)

/-- The word_headers / word_comment round trip through Models.lean: the direct
    table's headers must be readable back at the word index the layout says, which
    is the only place the offset fields do observable work outside this file. -/
def generateVkDirect_wordHeaders_ok : Bool :=
  let words : List VkTableWord :=
    [ { value := 11, label := "run_a[0]", headers := ["h1"] },
      { value := 12, label := "run_a[1]", headers := [] },
      { value := 13, label := "pool[0]", headers := ["h3"] } ]
  match generateVkDirect codecsV inputsV words with
  | .error _ => false
  | .ok vk =>
    vk.wordHeaders 31 == ["h1"] && vk.wordHeaders 32 == []
      && vk.wordHeaders 33 == ["h3"] && vk.wordHeaders 0 == []
      && vk.wordComment 32 == "run_a[1]" && vk.wordComment 0 == "vk_digest"

/-! ## generate_vk (VK:353-472) and the payload section ORDER -/

/-- THE ACCEPTANCE GATE hazard 7 asks for: the ORDER of the VK payload sections
    against VkPayloadLayout, pinned at the BYTE level and not by counts. A count
    check cannot see a swap of the quotient-constant and quotient-program sections;
    this can, because the two sections carry different labels and different values
    and because the byte offsets are named.
    PERTURBATION RUN: swapping the two reserve calls in VkPayloadLayout.forVk
    reddens this gate and generateVk_converges_ok; writing the program chunks at
    the const offset (a one-token swap at VK:444) reddens the label conjunct. -/
def payloadOrder_sectionsTiled_ok : Bool :=
  match generateVk Features.solidity envV codecsV inputsV with
  | .error _ => false
  | .ok vk =>
    match vk.payloadLayout with
    | .error _ => false
    | .ok layout =>
      let kinds := layout.sections.map (fun s => payloadSectionKindDebug s.kind)
      let wordOffsets := layout.sections.map (fun s => s.wordOffset)
      let byteOffsets := layout.sections.map (fun s => s.byteOffset)
      kinds == ["Header", "QuotientConstants", "QuotientProgram",
        "FixedCommitments", "PermutationCommitments"]
        && wordOffsets == [0, 31, 34, 36, 44]
        && byteOffsets == [0, 992, 1088, 1152, 1408]
        && layout.totalBytes == vk.len
        && ((vk.constants.drop 31).take 3).all (fun c => c.1 == "quotient_const")
        && ((vk.constants.drop 34).take 2).all (fun c => c.1 == "quotient_program")
        && vk.quotientConstOffsetWords == some 31
        && vk.quotientProgramOffsetWords == some 34

/-- The converged build field by field: three const words (101, 202, 303) written
    OVER the zero fill at the const offset, two program words at the program
    offset, and the four reservation fields set at the end and not before. The zero
    fill is what makes the write-back observable: a port that appended instead of
    overwriting would produce a table that is too long and trip the layout assert.
    PERTURBATION RUN: appending the consts instead of writing them in place reddens
    this gate and payloadOrder_sectionsTiled_ok; never writing back (leaving the
    zeros) reddens the three value conjuncts. -/
def generateVk_converges_ok : Bool :=
  match generateVk Features.solidity envV codecsV inputsV with
  | .error _ => false
  | .ok vk =>
    vk.constants.length == 36
      && vk.constants.getD 31 ("", 0) == ("quotient_const", 101)
      && vk.constants.getD 32 ("", 0) == ("quotient_const", 202)
      && vk.constants.getD 33 ("", 0) == ("quotient_const", 303)
      && vk.quotientConstWords == 3
      && vk.quotientProgramWords == 2
      && vk.len == 36 * 32 + 5 * 128
      && isOkS (vk.validatePayloadLayout)
      && ((vk.constants.drop 34).take 2).map (fun c => c.2.toNat) != [0, 0]

/-- THE REACHABLE PANICS of generate_vk, each at its own site: the reservation never
    converging (VK:396), the bytecode changing after materialisation (VK:457), and
    the constants changing after materialisation (VK:461).
    The VK:396 arm needs a candidate that GROWS on every iteration - a constant
    over-large candidate does NOT do it, because the loop converges as soon as the
    reservation reaches it, which is the first thing this gate got wrong and is why
    the stub below reads the address the reservation moved. That is exactly the
    feedback VK:355-357 describes: the program depends on memory addresses and the
    addresses depend on the VK length.
    PERTURBATION RUN: this gate is the evidence. Deleting the VK:457 unless reddens
    only its conjunct; deleting the VK:396 arm turns the panic into a wrong answer
    and reddens the third conjunct. -/
def generateVk_panics_ok : Bool :=
  let envBytes : VkBuildEnv Nat :=
    { envV with buildQuotientProgramItems := fun _ =>
        Except.ok { buildV with bytes := ByteArray.mk ((List.replicate 40 17).map Nat.toUInt8).toArray } }
  let envConsts : VkBuildEnv Nat :=
    { envV with buildQuotientProgramItems := fun _ =>
        Except.ok { buildV with consts := [9, 9, 9] } }
  let growEnv : VkBuildEnv Nat :=
    { envV with compactQuotientProgramFor := fun _ data => do
        -- the first fixed commitment's address, which Data.new derives as
        -- VK_MPTR + constants.len() words (ENC:309), so it grows with the
        -- reservation: exactly the feedback VK:355-357 describes.
        let basePtr := (data.fixedComms.head?).map (fun c => c.base.value)
        let base ← Value.asUsize (basePtr.getD valueDefault)
        Except.ok { buildV with consts := List.replicate (base / 32 + 1) 5 } }
  let envBig : VkBuildEnv Nat :=
    { envV with
      compactQuotientProgramFor := fun _ _ => Except.ok { buildV with consts := List.replicate 40 5 },
      buildQuotientProgramItems := fun _ => Except.ok { buildV with consts := List.replicate 40 5 } }
  panickedAtSite (generateVk Features.solidity envBytes codecsV inputsV) (vkSite 457)
    && panickedAtSite (generateVk Features.solidity envConsts codecsV inputsV) (vkSite 461)
    && panickedAtSite (generateVk Features.solidity growEnv codecsV inputsV) (vkSite 396)
    && isOkV (generateVk Features.solidity envV codecsV inputsV)
    -- CONTROL: a constant over-large candidate CONVERGES rather than failing to,
    -- because the loop breaks as soon as the reservation reaches the candidate.
    -- That is the conjunct that says the third one is about growth and not about
    -- size - and it is a conjunct this gate got wrong the first time, when only the
    -- compact stub was enlarged and the items stub was not, so the panic that came
    -- out was VK:461 and the control was silently testing something else.
    && isOkV (generateVk Features.solidity envBig codecsV inputsV)

/-- HAZARD 5, ANSWERED HONESTLY: the assert at VK:434-437 ("quotient const table
    exceeded VK payload reservation") and its sibling at VK:438-441 RESTATE the
    loop's own break condition at VK:384-386 over the same value, so no input can
    fire them. The perturbation the plan asked for was attempted and it FAILED to
    redden the site: a stub whose surviving build is larger than the reservation it
    converged on cannot be constructed, because convergence is defined as "not
    larger". What fires instead is VK:461, which is the first conjunct here and the
    second half of the evidence. The same holds of the two section-length asserts
    (VK:414, VK:420) and the byte-length assert (VK:426): each compares
    VkPayloadLayout::for_vk's own output against the quantity it was built from. All
    five are ported anyway, per R1 and R4, and they are regression guards on the
    LAYOUT code rather than on the input - which is what the report says.
    PERTURBATION RUN: the env below makes the compact build smaller than the items
    build, the closest reachable thing to an over-long const table; the panic that
    comes out is VK:461 and NOT VK:436, and this gate asserts exactly that. -/
def generateVk_hazard5_ok : Bool :=
  let envSmaller : VkBuildEnv Nat :=
    { envV with compactQuotientProgramFor := fun _ _ =>
        Except.ok { buildV with consts := [1, 2] } }
  let r := generateVk Features.solidity envSmaller codecsV inputsV
  panickedAtSite r (vkSite 461) && ! panickedAtSite r (vkSite 436)
    && ! panickedAtSite r (vkSite 438)


/-! ## The transcript and memory cluster (VK:549-653) -/

/-- VK:610-653. The three arguments the reference passes to from_protocol are pinned
    individually - proof_cptr 0, meta.num_evals (NOT num_main_evals) and
    meta.num_point_sets - because the second is the one a port reaches for by habit,
    and with the feature off the two are equal, so the mistake is invisible to the
    deployed fixture. The gate therefore also runs a meta whose dummy evals are
    non-zero, where the two differ.
    PERTURBATION RUN: passing num_main_evals reddens the second conjunct on the
    with-dummies meta; passing numDummyEvals where numPointSets belongs reddens the
    first conjunct (the recomputation on the right-hand side uses numEvals);
    passing numInstances as the proof_cptr reddens the first conjunct too. -/
def transcriptBufferLayoutForMeta_ok : Bool :=
  let m := inputsV.meta_
  let withDummies := m.setNumDummyEvals 4
  match transcriptBufferLayoutForMeta m 3 with
  | .error _ => false
  | .ok t =>
    t.words == orNat (do
        let p ← ProofCalldataLayout.fromProtocol m.protocol 0 m.numEvals m.numPointSets
        Except.ok (TranscriptBufferLayout.fromProofLayout p 3
          m.protocol.numUserChallenges).words) 999
      && (match transcriptBufferLayoutForMeta withDummies 3 with
          | .error _ => false
          | .ok t2 => t2.words != t.words)
      -- numInstances 0 gives the SAME bound: for this meta the dominating run is
      -- the eval block (VK:626-627's arm (b)), not the initial absorb, so the
      -- instance count cannot move the max. A thousand instances does move it, and
      -- that is the discriminating arm rather than a silent 0-vs-3.
      && (match transcriptBufferLayoutForMeta m 0 with
          | .error _ => false
          | .ok t3 => t3.words == t.words)
      && (match transcriptBufferLayoutForMeta m 1000 with
          | .error _ => false
          | .ok t4 => t4.words > t.words)

/-- VK:601-608, the #[cfg(test)] helper: the same number as the function it exposes,
    by construction, and pinning that keeps the helper from drifting. -/
def transcriptBufferWordsBound_ok : Bool :=
  match transcriptBufferLayoutForMeta inputsV.meta_ 3,
      transcriptBufferWordsBound inputsV.meta_ 3 with
  | .ok t, .ok w => t.words == w
  | _, _ => false

/-- VK:562-599. All six candidate ends computed independently and the max taken over
    them, plus the two conjuncts that make the max meaningful: the result is at
    least each candidate, and it changes when the dominating candidate changes. The
    dominating term for this fixture is the transcript end, which is the one that
    grows with the proof shape - the reason VK:578-583's comment says the buffer
    must stay below VK_MPTR at all.
    PERTURBATION RUN: dropping the quotient-return candidate from the list reddens
    the equality conjunct only when the quotient term dominates, so the gate also
    runs a meta with 400 simple selectors, where it does dominate and the omission
    shows. Dropping the pairing-batch end reddens nothing on this fixture, and that
    is stated rather than hidden: it is dominated by the transcript end, which is
    why the reference lists it "explicitly so the bound survives if that derivation
    changes" (VK:586-588). -/
def staticWorkingMemorySizeForMeta_ok : Bool :=
  let m := inputsV.meta_
  match staticWorkingMemorySizeForInputs inputsV m with
  | .error _ => false
  | .ok v =>
    let tw := (orNat (transcriptBufferLayoutForMeta m inputsV.numInstances)
      transcriptBufferLayoutDefault).words
    let candidates : List Nat :=
      [ transcriptBufferStart + tw * wordBytes,
        pcsPairingScratchStart + staticWorkingMemorySize * wordBytes,
        accumulatorPairingBatchPtr + accumulatorPairingBatchHashBytes,
        finalPairingScratchStart + pairingStaticWorkingWords * wordBytes,
        verifierReturnBufferStart + wordBytes,
        quotientReturnBufferStart + (2 + m.numSimpleSelectors) * wordBytes ]
    candidates.length == 6 && v == (natMaximum candidates).getD 0
      && candidates.all (fun c => c <= v)
      && v == candidates.head?.getD 0
      && (match staticWorkingMemorySizeForInputs inputsV
            { m with numSimpleSelectors := 400 } with
          | .error _ => false
          | .ok v2 => v2 == quotientReturnBufferStart + (2 + 400) * wordBytes && v2 > v)

/-- VK:549-561 against the stub planner: the two config fields the reference fills
    arrive at the callee, and the fields it does not touch arrive unchanged from the
    default. This is the gate that makes the threaded hole observable - the stub
    copies the two fields into readable layout fields precisely so that a port that
    forgot VK:557-559 goes red.
    PERTURBATION RUN: deleting the transcriptWords assignment reddens the first
    conjunct; deleting numInstances reddens the second; passing
    verifierMemoryLayoutConfigDefault instead of the incoming config reddens the
    third. -/
def memoryLayoutFor_config_ok : Bool :=
  let expected := orNat
    (Except.map (fun t => t.words) (transcriptBufferLayoutForMeta inputsV.meta_
      inputsV.numInstances)) 999
  match memoryLayoutForInputs envV inputsV inputsV.meta_ renderVkV
      (ptrMemory (valueFromNat 0x4000)) verifierMemoryLayoutConfigDefault with
  | .error _ => false
  | .ok mem =>
    mem.transcriptMptr == expected
      && mem.verifierReturnMptr == inputsV.numInstances
      && mem.pcs.rotPointsWords == pcsMemoryRequirementsDefault.rotPointsWords
      && mem.scalarInvScratchMptr == memV.scalarInvScratchMptr
      && ptrBeq mem.vkMptr (ptrMemory (valueFromNat 0x4000))

/-- VK:474-523, the feature-off arm: n_dummy is 0, so num_evals is unchanged, no
    dummy words are written, and the meta that comes back differs from the input
    only in num_point_sets.
    PERTURBATION RUN: forcing n_dummy to 1 reddens the first three conjuncts;
    calling setNumDummyEvals with mainEvals instead of n reddens the second. -/
def metaDataForVk_featureOff_ok : Bool :=
  match metaDataForVkInputs Features.solidity envV inputsV renderVkV
      (ptrMemory (valueFromNat 0x4000)) with
  | .error _ => false
  | .ok (meta_, data, mem) =>
    meta_.numDummyEvals == 0
      && meta_.numEvals == inputsV.meta_.numEvals
      && data.dummyEvalWords.isEmpty
      && meta_.numPointSets == orNat (numPointSets inputsV.meta_ data) 999
      && meta_.numPointSets > 0
      && ptrBeq mem.vkMptr (ptrMemory (valueFromNat 0x4000))

/-- The point-set ordering claim of VK:519-522, checked through the stub's recorded
    config: the layout the function returns was built from a meta whose
    num_point_sets is the planned count. Reordering VK:519-521 so the layout is
    built before the count is set changes the transcript bound whenever the
    point-set count affects the proof layout, which it does: from_protocol reads
    num_point_sets (AP:126) and the q_eval sections depend on it.
    PERTURBATION RUN: swapping the last two statements of metaDataForVk reddens the
    first conjunct. -/
def metaDataForVk_pointSetsOrder_ok : Bool :=
  match metaDataForVkInputs Features.solidity envV inputsV renderVkV
      (ptrMemory (valueFromNat 0x4000)) with
  | .error _ => false
  | .ok (meta_, _, mem) =>
    mem.transcriptMptr == orNat
      (Except.map (fun t => t.words) (transcriptBufferLayoutForMeta meta_
        inputsV.numInstances)) 999
      && meta_.numPointSets == orNat
          (numPointSets meta_ (orNat (Data.new meta_ renderVkV mem) dataEmptyStub)) 998

/-- The feature-ON arm (R8's second branch): with outer-fewer-point-sets the dummy
    count comes from num_dummy_queries on the RAW data, num_evals grows by it, and
    the dummy words are written. Both arms are gated because the reference has both,
    and because the deployed profile is the off arm - so the on arm is the one nobody
    runs in production and the one most likely to rot.
    PERTURBATION RUN: hard-coding n_dummy to 0 reddens the second and third
    conjuncts whenever the fixture's dummy count is non-zero; deleting the
    n_dummy > 0 guard (always calling set_dummy_eval_words) reddens
    metaDataForVk_featureOff_ok. -/
def metaDataForVk_featureOn_ok : Bool :=
  let feat : Features := { Features.solidity with outerFewerPointSets := true }
  match metaDataForVkInputs feat envV inputsV renderVkV
      (ptrMemory (valueFromNat 0x4000)) with
  | .error _ => false
  | .ok (meta_, data, _) =>
    meta_.numDummyEvals == orNat (numDummyQueries inputsV.meta_
        (orNat (Data.new inputsV.meta_ renderVkV memV) dataEmptyStub)) 997
      && meta_.numEvals == inputsV.meta_.numEvals + meta_.numDummyEvals
      && data.dummyEvalWords.length == meta_.numDummyEvals

/-- VK:525-547. The loop converges on the first iteration for this fixture - the
    starting VK_MPTR is computed from the same meta the first pass returns - and the
    returned pointer is the one the planner asked for.
    PERTURBATION RUN: changing the loop bound from 3 to 2 reddens nothing here,
    because the fixture settles on the second iteration; that is stated rather than
    hidden, and it is why the panic arm below is a real attempt and not a formality. -/
def metaDataForStableStaticLayout_ok : Bool :=
  match metaDataForStableStaticLayoutInputs Features.solidity envV inputsV renderVkV with
  | .error _ => false
  | .ok (vkMptr, meta_, data, _) =>
    -- the pointer that came back is the one the PLAN asked for, which is not the
    -- pointer the loop started from: the starting VK_MPTR is computed from the raw
    -- meta, and setting num_point_sets moves the transcript bound (9024 to 9184
    -- here), so the second iteration is the one that settles.
    ptrBeq vkMptr (ptrMemory (valueFromNat
      (orNat (staticWorkingMemorySizeForInputs inputsV meta_) 999)))
      && orNat (staticWorkingMemorySizeForInputs inputsV inputsV.meta_) 999
          != orNat (staticWorkingMemorySizeForInputs inputsV meta_) 998
      && meta_.numPointSets > 0
      && data.dummyEvalWords.isEmpty

/-! ## The one panic site this package could NOT reach

VK:546 - "static verifier memory layout did not converge after proof-shape
planning" - is ported (metaDataForStableStaticLayout's final arm), but NO stub in
this file can fire it, and the attempts are recorded here rather than dropped,
because a panic site with no demonstrated failure mode is exactly the R-38 / R-41
shape this project keeps hitting.

What was tried, and why each one converged instead:
* a planner stub that adds a constant to the transcript word count - the added
  words do not feed back into the plan, because staticWorkingMemorySizeForMeta
  reads the transcript bound from the META, not from the layout;
* a stub that aliases commsMptrBase onto VK_MPTR, and one that aliases the advice
  commitment base onto VK_MPTR plus the constant-table length (so the aliasing
  moves as the reservation moves): both settle on the second iteration, because
  num_point_sets depends on the EQUALITY PATTERN of the commitment pointers and
  not on their addresses, and a uniform shift preserves the pattern;
* a stub whose advice base alternates with the parity of the constant-table
  length: also converges, for the same reason.

The structural fact behind all three is that the plan can only move through
num_point_sets, and num_point_sets is address-invariant under the pointer model
Data.new uses. So VK:546 is, like VK:436 and VK:438, a guard against a FUTURE
change to the planner rather than a reachable input today - and unlike those three
it is not even restated from a loop condition, it is genuinely the "no fixed point
in three steps" case that the reference's own comment at VK:527-529 describes.
It stays ported per R1 and R4. No gate is claimed for it. -/

/-! ## R11 evidence: the struct itself -/

/-- MOD:37-45 read back: six fields in the Rust's order, and the two that vk.rs
    never reads are still carried. A reviewer checking R11 against the Rust should
    be able to see that the port did not quietly drop the fields it has no use for. -/
def verifierBuildInputs_fields_ok : Bool :=
  inputsV.numInstances == 3 && inputsV.numCommittedInstances == 1
    && (match inputsV.accEncoding with
        | some e => e.numLimbs == 7 && e.numLimbBits == 56 && e.offset == 4
        | none => false)
    && inputsV.meta_.numEvals == Midfall.Generator.EncodingKats.metaFixture.numEvals
    && inputsV.params.gLagrange.length == 4
    && expOf inputsV.params.g2 == 1 && expOf inputsV.params.sG2 == 3
    && inputsV.vk.domain.k == 2 && inputsV.vk.transcriptRepr.val == 7

#eval fixtureDomain_ok -- expect true
#eval fixturePointsDistinct_ok -- expect true
#eval vkHeaderSlot_word_ok -- expect true
#eval vkHeaderField_agreesWithTable_ok -- expect true
#eval vkHeaderBuilder_fullOk_ok -- expect true
#eval vkHeaderBuilder_duplicateErr_ok -- expect true
#eval vkHeaderBuilder_widthErr_ok -- expect true
#eval vkHeaderBuilder_overflowErr_ok -- expect true
#eval vkHeaderBuilder_finishMissingErr_ok -- expect true
#eval omegaPowers_accumulatorEquivalence_ok -- expect true
#eval srsTauCommitment_semantics_ok -- expect true
#eval srsTauIsConsistent_honestSrs_ok -- expect true
#eval srsFingerprint_preimage_ok -- expect true
#eval srsFingerprint_fieldOrder_ok -- expect true
#eval generateBaseVk_header_ok -- expect true
#eval generateBaseVk_g1g2Slots_ok -- expect true
#eval generateBaseVk_srsAsserts_ok -- expect true
#eval generateBaseVk_comms_ok -- expect true
#eval generateBaseVk_accEncoding_ok -- expect true
#eval generateBaseVk_omegaInvToL_ok -- expect true
#eval generateVkDirect_table_ok -- expect true
#eval generateVkDirect_empty_ok -- expect true
#eval generateVkDirect_wordHeaders_ok -- expect true
#eval payloadOrder_sectionsTiled_ok -- expect true
#eval generateVk_converges_ok -- expect true
#eval generateVk_panics_ok -- expect true
#eval generateVk_hazard5_ok -- expect true
#eval transcriptBufferLayoutForMeta_ok -- expect true
#eval transcriptBufferWordsBound_ok -- expect true
#eval staticWorkingMemorySizeForMeta_ok -- expect true
#eval memoryLayoutFor_config_ok -- expect true
#eval metaDataForVk_featureOff_ok -- expect true
#eval metaDataForVk_pointSetsOrder_ok -- expect true
#eval metaDataForVk_featureOn_ok -- expect true
#eval metaDataForStableStaticLayout_ok -- expect true
#eval verifierBuildInputs_fields_ok -- expect true

end Midfall.Generator.VkKats
