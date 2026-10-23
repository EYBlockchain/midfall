-- |
-- Midfall.Halo2.Exec.Kzg.Msm
--
-- The two-channel multi-scalar-multiplication accumulator and the final
-- pairing check (rust: proofs/src/poly/kzg/msm.rs). This is the end of the
-- verifier: everything Exec/Verifier builds feeds into DualMSM.check.
--
-- The Rust MSM back ends (blstrs multi_exp, msm_best) are performance
-- machinery over affine coordinates and fixed windows. Semantically an MSM
-- is a sum of scalar multiples, which is what the port computes: exact gas
-- and prover performance are out of scope (plan Section 1) and the proofs
-- only need the value. The one observable detail of the back end is kept:
-- msm_specific drops zero coefficients, and the zip that pairs coefficients
-- with bases truncates to the shorter input (rule R3).

import Midfall.Common.Curve
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Query
import Midfall.Halo2.Exec.Kzg.Params

namespace Midfall.Halo2

-- Only p is a file-level variable: it is determined by every signature that
-- mentions Fr p. The group binders are written out per declaration on purpose.
-- Gₜ in particular cannot be a file-level variable for DualMSM.check, because
-- Lean only threads a variable into a declaration when the *signature* pins it,
-- and the pairing target appears in no signature unless DualMSM carries it as a
-- phantom parameter (which it does, and which is why it is a phantom).
variable {p : ℕ} [Fact (Nat.Prime p)]


/-- Scalar multiplication on a point. The port writes the groups
    multiplicatively (as the plan and the Rust do) while the scalar action is
    the Module on the additive form (D-P1). -/
def gsmul {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (s : Fr p) (Q : G₁) : G₁ :=
  Additive.toMul (s • Additive.ofMul Q)

/-- A Decidable witness as a Bool: the bridge from an equation over an
    abstract group to the Bool-typed checks of plan 9.2. -/
def decideBool {α : Type} {a b : α} (d : Decidable (a = b)) : Bool :=
  match d with
  | .isTrue _ => true
  | .isFalse _ => false

/-- rust: proofs/src/poly/kzg/msm.rs:163-191 (msm_specific).

    coeffs.iter().zip(bases) truncates to the shorter input, then zero
    coefficients are dropped (the Rust comment says so), then the empty case
    returns the identity. Dropping zeros is a semantic no-op in a group -
    0 • B is the identity - but the truncation is not: a length mismatch
    silently ignores the tail, and the port must ignore the same tail. -/
def msmSpecific {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (coeffs : Array (Fr p)) (bases : Array G₁) : G₁ :=
  ((List.zip coeffs.toList bases.toList).filterMap
    fun (s, b) => if s = 0 then none else some (s, b)).foldl
    (fun acc (s, b) => acc * gsmul s b) 1

/-- rust: proofs/src/poly/kzg/msm.rs:29-34 (struct MSMKZG). The three vectors
    are kept in lockstep by every constructor below: that is the invariant Wf. -/
structure MSMKZG (F G : Type) where
  scalars : Array F
  bases : Array G
  labels : Array CommitmentLabel

/-- The three vectors have the same length. Every Rust constructor
    establishes it; it is what makes the Rust bases[0] in eval unreachable
    as a panic. -/
def MSMKZG.Wf {F G : Type} (m : MSMKZG F G) : Prop :=
  m.scalars.size = m.bases.size ∧ m.bases.size = m.labels.size

namespace MSMKZG

/-- rust: msm.rs:119-128 (add_msm): extend each vector with the other MSM. -/
def addMsm {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (m other : MSMKZG (Fr p) G₁) : MSMKZG (Fr p) G₁ :=
  { scalars := m.scalars ++ other.scalars
    bases := m.bases ++ other.bases
    labels := m.labels ++ other.labels }

/-- rust: msm.rs:38-44 (init). -/
def init {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] : MSMKZG (Fr p) G₁ :=
  { scalars := #[], bases := #[], labels := #[] }

/-- rust: msm.rs:47-65 (from_many): concatenate a list of MSMs, in order. The
    Rust appends with Vec::append, which is order-preserving. -/
def fromMany {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (msms : Array (MSMKZG (Fr p) G₁)) : MSMKZG (Fr p) G₁ :=
  msms.foldl (fun acc m => acc.addMsm m) init

/-- rust: msm.rs:68-74 (from_base): one term, scalar 1, NoLabel. -/
def fromBase {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (base : G₁) : MSMKZG (Fr p) G₁ :=
  { scalars := #[1], bases := #[base], labels := #[CommitmentLabel.noLabel] }

/-- rust: msm.rs:113-117 (append_term). -/
def appendTerm {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (m : MSMKZG (Fr p) G₁) (scalar : Fr p) (point : G₁)
    (label : CommitmentLabel) : MSMKZG (Fr p) G₁ :=
  { m with
      scalars := m.scalars.push scalar
      bases := m.bases.push point
      labels := m.labels.push label }

/-- rust: msm.rs:130-134 (scale): multiply every scalar by factor. The Rust
    maps in parallel; order is irrelevant. -/
def scale {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (m : MSMKZG (Fr p) G₁) (factor : Fr p) : MSMKZG (Fr p) G₁ :=
  { m with scalars := m.scalars.map (fun s => s * factor) }

/-- rust: msm.rs:140-146 (eval).

    The Rust shortcut compares the whole scalars vector with vec![ONE], not
    just its length, and then indexes bases[0]. R4 note: that index is a
    panic site in Rust when bases is empty. Under Wf it cannot happen, so the
    port uses getD with the identity as fallback to stay total (rule R10);
    Phase 4 proves the fallback unreachable. -/
def eval {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (m : MSMKZG (Fr p) G₁) : G₁ :=
  if m.scalars.toList = [1] then
    m.bases.getD 0 1
  else
    msmSpecific m.scalars m.bases

/-- rust: msm.rs:136-138 (check): the MSM evaluates to the identity. -/
def check {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ] (m : MSMKZG (Fr p) G₁) : Bool :=
  decideBool (P.decEqG₁ (eval m) 1)

/-- rust: msm.rs:94-106 (collapse): evaluate and replace the terms with the
    single result. The Rust debug_assert that every label is NoLabel or
    Advice is compiled out in the reference profile (BASELINE.md: release),
    so the port does not enforce it either - recorded here because a debug
    build would panic where a release build silently collapses. -/
def collapse {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] (m : MSMKZG (Fr p) G₁) : MSMKZG (Fr p) G₁ :=
  fromBase (eval m)

end MSMKZG

/-- rust: proofs/src/utils/arithmetic.rs:275-299 (msm_inner_product).
    Verifier-reachable at poly/kzg/mod.rs:401 and :507, both inside
    multi_prepare. It lives here rather than in Exec/Arith because its
    domain and codomain are MSMKZG (plan Section 4 module map).

    The Rust zips msms.iter_mut() against scalars.iter(), so a shorter
    scalar slice silently drops the *tail of the MSMs* - and a dropped MSM
    is never scaled and never contributes, rather than being an error. The
    port keeps that truncation exactly (rule R3). Each retained MSM is
    scaled in place and then concatenated, which is addMsm of scale. -/
def msmInnerProduct {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p]
    [Module (ZMod p) (Additive G₁)]
    (msms : Array (MSMKZG (Fr p) G₁)) (scalars : Array (Fr p)) :
    MSMKZG (Fr p) G₁ :=
  (List.zip msms.toList scalars.toList).foldl
    (fun acc (msm, s) => acc.addMsm (msm.scale s)) MSMKZG.init

/-! rust: proofs/src/utils/arithmetic.rs:320-344 (trait MSM). NOT ported as a
    structure of functions, and that is a decision rather than an omission:
    rule R9 names PolynomialCommitmentScheme, Transcript, Hashable and Guard
    - the traits with more than one instantiation in the verifier. MSM has
    exactly one, MSMKZG, and its eight methods are the definitions above
    (appendTerm, addMsm, scale, check, eval, init/fromMany, and the structure
    projections for bases/scalars/labels). A record of function pointers
    would be a second name for every call site, free to drift from the first.
    If a second MSM ever appears - a batched or in-circuit one - that is the
    moment to introduce it. -/
/-- rust: msm.rs:194-198 (struct DualMSM): a left and a right channel.

    The Rust is DualMSM<E> with only G1 components; G₂ and Gₜ are phantom
    parameters here. They are not decoration: the final check needs the
    pairing, and the pairing target group appears in no data-carrying type, so
    without a phantom parameter there is nothing to pin it and the instance
    cannot be resolved at the call site in Exec/Native. -/
structure DualMSM (F G₁ G₂ Gₜ : Type) where
  left : MSMKZG F G₁
  right : MSMKZG F G₁

namespace DualMSM

/-- rust: msm.rs:241-246 (init), and the Default impl at 214-221. -/
def init {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] {G₂ Gₜ : Type} : DualMSM (Fr p) G₁ G₂ Gₜ :=
  { left := MSMKZG.init, right := MSMKZG.init }

/-- rust: msm.rs:249-251 (new). -/
def new {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] {G₂ Gₜ : Type}
    (left right : MSMKZG (Fr p) G₁) : DualMSM (Fr p) G₁ G₂ Gₜ :=
  { left, right }

/-- rust: msm.rs:271-274 (scale): both channels. -/
def scale {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] {G₂ Gₜ : Type}
    (g : DualMSM (Fr p) G₁ G₂ Gₜ) (e : Fr p) : DualMSM (Fr p) G₁ G₂ Gₜ :=
  { g with left := g.left.scale e, right := g.right.scale e }

/-- rust: msm.rs:277-280 (add_msm). -/
def addMsm {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] {G₂ Gₜ : Type}
    (g other : DualMSM (Fr p) G₁ G₂ Gₜ) : DualMSM (Fr p) G₁ G₂ Gₜ :=
  { g with left := g.left.addMsm other.left, right := g.right.addMsm other.right }

/-- rust: msm.rs:254-268 (split): the labelled terms of both channels, for the
    trace and for the contract lowering. izip! truncates to the shortest of
    the three vectors, like the zip in msm_specific. -/
def split {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)] {G₂ Gₜ : Type}
    (g : DualMSM (Fr p) G₁ G₂ Gₜ) :
    Array (CommitmentLabel × Fr p × G₁) × Array (CommitmentLabel × Fr p × G₁) :=
  let one (m : MSMKZG (Fr p) G₁) :=
    ((List.zip (List.zip m.labels.toList m.scalars.toList) m.bases.toList).map
      fun ((l, s), b) => (l, s, b)).toArray
  (one g.left, one g.right)

/-- rust: msm.rs:284-308 (check), the final pairing equation
    e(left, sG2) * e(right, -G2) = 1.

    AdmissiblePairing.e is a curried LinearMap, so the two terms are added in
    the additive form of Gₜ and converted back with Additive.toMul, which is
    the multiplicative product the plan writes; the identity of Gₜ is 1 in
    that notation and 0 in the additive one, and the Rust tests
    final_exponentiation().is_identity().

    The Rust recomputes the left-channel one-scalar shortcut before calling
    eval; that shortcut is already inside eval, so the port keeps one copy
    instead of duplicating a no-op branch. The pairing *inputs* are what the
    conformance harness compares (plan Section 5), and the reorder lemma of
    plan Section 6 relates this orientation to the contract orientation
    e(right,G2) * e(left,-sG2) = 1. -/
def check {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂) : Bool :=
  let left := g.left.eval
  let right := g.right.eval
  decideBool (P.decEqGₜ
    (Additive.toMul
      (P.e (Additive.ofMul left) (Additive.ofMul params.sG2Prepared) +
       P.e (Additive.ofMul right) (Additive.ofMul params.nG2Prepared))) 1)

/-- rust: msm.rs:223-234 (impl Guard<F, KZGCommitmentScheme<E>> for DualMSM):
    verify = check or Error::OpeningError. This is where the Guard trait of
    rule R9 is instantiated for KZG. -/
def verify {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (g : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂) :
    Except Fault Unit :=
  if check g params then .ok () else .error (Fault.error Error.opening)

end DualMSM

end Midfall.Halo2
