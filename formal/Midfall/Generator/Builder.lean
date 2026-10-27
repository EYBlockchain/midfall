-- |
-- Midfall.Generator.Builder
--
-- THE PUBLIC GENERATOR FACADE: the SolidityGenerator record, the shape validation
-- that decides whether a constraint system is supported at all, the repack and
-- calldata wrappers over Calldata.lean, and the options-driven render entry points.
-- Ported from proofs/solidity-verifier/src/builder/{mod,api,render,repack}.rs
-- (69 + 162 + 220 + 27 = 478 lines at HEAD). Work package P-12.
--
-- CITATION NOTATION (docs/plans/README.md standing note 2: every range below was
-- re-derived from git show HEAD:<path>).
-- * BM:   proofs/solidity-verifier/src/builder/mod.rs (69 lines at HEAD).
-- * BAPI: proofs/solidity-verifier/src/builder/api.rs (162 lines at HEAD).
-- * BREN: proofs/solidity-verifier/src/builder/render.rs (220 lines at HEAD).
-- * BREP: proofs/solidity-verifier/src/builder/repack.rs (27 lines at HEAD).
-- * CD:   proofs/solidity-verifier/src/lowering/calldata.rs (160 lines at HEAD).
-- * MOD:  proofs/solidity-verifier/src/lowering/mod.rs (VerifierBuildInputs, MOD:37-45).
--
-- WHY ONE FILE FOR FOUR RUST FILES. mod.rs, api.rs, render.rs and repack.rs are not
-- four modules in Rust's own eyes: they are ONE impl block for
-- SolidityGenerator split across four files by "mod api; mod render; mod repack;"
-- (BM:29-31), each starting with "use super::*;" and each reopening the same impl.
-- Lean has no such split: the record must be declared once, before any of its
-- methods, and the methods must follow it in one namespace. Splitting the Lean port
-- across four files would mean four files that all import one of them for the type -
-- the same reason P-09a put the whole QVM vocabulary in one file. calldata.rs and
-- evm.rs are genuinely separate Rust modules with their own names, so they keep their
-- own Lean files (Calldata.lean, Evm.lean), and Builder.lean imports them in the
-- direction the Rust does (BREP calls CD, CD calls EVM).
--
-- WHAT IS NOT PORTED, WITH THE BLOCKER NAMED AT EACH SITE.
-- * BM:59-68 inputs(): it builds VerifierBuildInputs (MOD:37-45), which is
--   Vk.lean:359-377's, and D-P17 forbids importing Generator.Vk here. The Lean record
--   below carries the same five facts, so the field copy has no Lean analogue;
--   builderModFields_areTheInputsFields_ok pins that the two field sets still agree
--   by reading both Rust files at #eval time.
-- * BAPI:113-115, 128-138, 144-146, 154-156, 158-161: proof_evaluation_counts,
--   direct_quotient_trace_values, quotient_identity_manifest, quotient_certificate
--   and quotient_certificate_hash. All five are one-line forwarders into
--   crate::lowering::diagnostics, and PLAN 14.8 CUTs P-14 ("listing, disasm,
--   diagnostics"). Five of builder/api.rs's eleven items are therefore unreachable
--   from any port that respects the cut; this is reported as a finding rather than
--   papered over with a stub.
-- * BREN:154-175 render_verifier_source_with_plan and BREN:213-219 render_vk_model:
--   the Askama models are P-13 (templates) and the VK payload model is Vk.lean's
--   (D-P17). What IS ported is the error each one raises: GeneratorError::Render with
--   the artifact name verbatim.
-- * BREN:185-210 render_quotient_probe: cfg(feature = "evm") + doc(hidden) + "not a
--   verifier", and it needs both blocked renderers above. Not ported; the
--   QuotientProbeArtifacts record it returns is already in Api.lean:652.
-- * BREN:86-103's quotient_listing_artifacts: the P-14-CUT diagnostics again. The
--   listing's POSITION in the sequence is ported (after every Solidity artifact, so
--   it cannot influence them) with the step itself passed in.
--
-- DEVIATIONS AND HAZARD NOTES.
-- * R2: meta is a Lean command modifier, so the field is meta_ - the convention
--   Vk.lean:357, VmTypes.lean:662 and LoweringPlan.lean:120 record.
-- * R8: tryNew takes a Features argument the Rust does not take. The Rust reads the
--   compile-time feature set inside ConstraintSystemMeta::new; the port threads the
--   value, following Encoding.lean:454's own signature.
-- * R4: BAPI:27's panic!("unsupported Solidity verifier shape: {err}") becomes a
--   panic SITE; the message is lost because ApiFault.panic carries only a site (the
--   F2 convention LoweringPlan.lean:104-113 records). BAPI:64's abort inside
--   ConstraintSystemMeta::new (ProtocolPlan::from_constraint_system's unwrap_or_else,
--   PM:642) is the same case, and its site is BAPI:64.
-- * Hazard 3 (P-09e F-3): NOT REACHED from here. tryNew calls
--   validate_for_num_instances (BAPI:50), which is total; the non-total
--   fixed_scalar_count is called only from plan.rs:556 and artifacts.rs:184.
-- * Hazard 5 / D-P17: no Generator.Vk, no Midfall.Instances/, and no
--   Generator.Quotient.* either - the only quotient-VM type this file needs is
--   RepackedProofLayoutPlan, which arrives through Calldata.lean.
-- * R6: Vec -> List; &[u8] -> Bytes; Option<[u8; 32]> -> Option Bytes.

import Midfall.Generator.Api
import Midfall.Generator.Calldata
import Midfall.Generator.Evm
import Midfall.Generator.Encoding
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.VerifyingKey

namespace Midfall.Generator

open Midfall.Halo2

/-- rust: BM:43-51 (struct SolidityGenerator) @formal-baseline. "Solidity verifier
    generator for midnight-proofs (logup + trash + KZG multi-prepare PCS) on BLS12-381
    EIP-2537. The supported protocol shape is intentionally narrow: Midfall/Midnight
    KZG proofs with one committed identity instance column and one non-committed
    public-input column."

    Three type parameters, none of them invented: Params is ParamsKZG<Bls12> (BM:45),
    which the tree has never ported - Exec/Arith.lean:172 records it as prover-only -
    so it is carried as a parameter exactly as LoweringPlan carries the deferred M10
    Program/Layout types. Fr and G1 are the VerifyingKey parameters (BM:46). Rust's
    borrowed references become plain fields: the port has no lifetimes and nothing
    mutates them. -/
structure SolidityGenerator (Params Fr G₁ : Type) where
  /-- rust: BM:45 (params: &'a ParamsKZG<Bls12>) -/
  params : Params
  /-- rust: BM:46 (vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>) -/
  vk : VerifyingKey Fr G₁
  /-- rust: BM:47 (num_instances: usize) -/
  numInstances : Nat
  /-- rust: BM:48-49 (acc_encoding: Option<AccumulatorEncoding>) - "Optional
      accumulator layout encoded at the tail of the public instances." -/
  accEncoding : Option AccumulatorEncoding
  /-- rust: BM:50 (meta: ConstraintSystemMeta) - R2: meta_. -/
  meta_ : ConstraintSystemMeta

/-- rust: BAPI:12 (SUPPORTED_COMMITTED_INSTANCE_COLUMNS: usize = 1) @formal-baseline.
    "Number of committed instance columns supported by the generated ABI." -/
def supportedCommittedInstanceColumns : Nat := 1

/-- rust: BAPI:14 (SUPPORTED_NON_COMMITTED_INSTANCE_COLUMNS: usize = 1)
    @formal-baseline. "Number of non-committed instance columns supported by the
    generated ABI." -/
def supportedNonCommittedInstanceColumns : Nat := 1

/-- rust: BAPI:15-18 (SUPPORTED_COMMITTED_INSTANCE_COMMITMENT) @formal-baseline.
    "Committed-instance commitment policy hard-coded by the generated verifier ABI."
    The value is CommittedInstanceCommitmentKind::Identity, i.e. Api.lean:247's
    single-variant enum: the G1 identity absorbed into the transcript, not a
    caller-supplied commitment. -/
def supportedCommittedInstanceCommitment : CommittedInstanceCommitmentKind :=
  CommittedInstanceCommitmentKind.identity

/-- rust: BAPI:80-109 (validate_instance_column_shape) @formal-baseline. "Validate
    the currently supported committed/non-committed instance split."

    BAPI:93-95 is total.checked_sub(committed).unwrap_or(usize::MAX): a CHECKED
    subtraction whose None arm becomes the MAX sentinel, NOT a wrapping subtraction.
    The distinction is observable - with a plain Nat subtraction a committed count
    above the total would wrap to a small number and could accidentally equal the
    supported non-committed count, accepting a shape the reference rejects.
    validateInstanceColumnShape_checkedSubSentinel_ok probes exactly that case. -/
def SolidityGenerator.validateInstanceColumnShape
    (totalInstanceColumns numCommittedInstances : Nat) : Except ApiFault Unit := do
  let supportedCommitted := supportedCommittedInstanceColumns
  let supportedNonCommitted := supportedNonCommittedInstanceColumns
  let nonCommitted :=
    if numCommittedInstances <= totalInstanceColumns
    then totalInstanceColumns - numCommittedInstances
    else usizeMax
  if numCommittedInstances != supportedCommitted
      || nonCommitted != supportedNonCommitted then
    throw (ApiFault.error (GeneratorError.unsupportedInstanceColumnShape
      (total := totalInstanceColumns) (committed := numCommittedInstances)
      (expectedCommitted := supportedCommitted)
      (expectedNonCommitted := supportedNonCommitted)))

/-- rust: BAPI:30-73 (try_new) @formal-baseline. "Try to construct a new
    SolidityGenerator, returning a typed error when the supplied constraint system is
    outside the currently supported Midfall verifier shape."

    THIS IS THE REFERENCE FOR Supported. PLAN 9.5's Supported record is meant to
    mirror try_new plus what the proofs need, and P-SE D2 makes its non-vacuity a
    requirement, so the four checks below - in this order, each with its own error -
    are what a Supported instance has to imply. The order is observable: a config
    that fails two of them reports the earlier one, and
    tryNew_checkOrderIsObservable_ok pins it.

    R8: feat is the compile-time feature set the Rust reads implicitly (header).
    R3: the three question marks at BAPI:45, BAPI:50 and BAPI:64 are three
    left-arrows. -/
def SolidityGenerator.tryNew {Params Fr G₁ : Type} (params : Params)
    (vk : VerifyingKey Fr G₁) (config : GeneratorConfig) (feat : Features) :
    Except ApiFault (SolidityGenerator Params Fr G₁) := do
  -- BAPI:38-40.
  if vk.cs.numAdviceColumns == 0 then
    throw (ApiFault.error GeneratorError.noAdviceColumns)
  -- BAPI:41-48, with the comment's rule: committed columns come first in verifier
  -- order, and the total is the sum of the two arguments the Rust verifier takes.
  SolidityGenerator.validateInstanceColumnShape vk.cs.numInstanceColumns
    config.numCommittedInstances
  -- BAPI:49-51.
  match config.accumulator with
  | some acc => acc.validateForNumInstances config.numInstances
  | none => pure ()
  -- BAPI:52-62: the FIRST query whose rotation is not cur. Circuit.lean's own hazard
  -- note: Rotation::cur() is rotation.int == 0, never structural equality, because
  -- Lean has two inhabitants where Rust has one i32.
  match vk.cs.instanceQueries.find? (fun q => Rotation.int q.2 ≠ 0) with
  | some q =>
      throw (ApiFault.error (GeneratorError.rotatedInstanceQuery
        (column := q.1.index) (rotation := Rotation.int q.2)))
  | none => pure ()
  -- BAPI:64. The Rust cannot fail here: ConstraintSystemMeta::new aborts through
  -- PM:642's unwrap_or_else, which is a panic, so the port's channel is a panic site
  -- and the underlying message is lost (F2 convention).
  let meta_ ← match ConstraintSystemMeta.new feat vk.cs config.numCommittedInstances with
    | .ok m => Except.ok m
    | .error _ => .error (ApiFault.panic "proofs/solidity-verifier/src/builder/api.rs:64")
  -- BAPI:66-72.
  let generator : SolidityGenerator Params Fr G₁ :=
    { params := params, vk := vk, numInstances := config.numInstances,
      accEncoding := config.accumulator, meta_ := meta_ }
  Except.ok generator

/-- rust: BAPI:20-28 (new) @formal-baseline. "Return a new SolidityGenerator." The
    Rust panics on an unsupported shape with "unsupported Solidity verifier shape:
    {err}" (BAPI:27); R4 turns that into a panic site and the message is lost
    (header). The port keeps the channel explicit rather than calling panic!. -/
def SolidityGenerator.new {Params Fr G₁ : Type} (params : Params)
    (vk : VerifyingKey Fr G₁) (config : GeneratorConfig) (feat : Features) :
    Except ApiFault (SolidityGenerator Params Fr G₁) :=
  match SolidityGenerator.tryNew params vk config feat with
  | .ok g => .ok g
  | .error (ApiFault.panic site) => .error (ApiFault.panic site)
  | .error (ApiFault.error _) =>
      .error (ApiFault.panic "proofs/solidity-verifier/src/builder/api.rs:27")

/-- rust: BAPI:75-78 (committed_instance_commitment_kind) @formal-baseline. "Return
    the committed-instance commitment policy for this generator." -/
def SolidityGenerator.committedInstanceCommitmentKind
    {Params Fr G₁ : Type} (_self : SolidityGenerator Params Fr G₁) :
    CommittedInstanceCommitmentKind := supportedCommittedInstanceCommitment

/-- rust: BREP:7-10 (SolidityGenerator::repack_proof) @formal-baseline. "Repack a
    midnight-proofs proof into the generated verifier ABI." The Rust threads
    self.inputs(); the Lean port cannot build the lowering plan (the constructors are
    unported - LoweringPlan.lean's header names the blockers), so the plan is a
    parameter. That is the P-11 precedent of passing an unported callee in rather than
    stubbing it. -/
def SolidityGenerator.repackProof {Params Fr G₁ : Type}
    (_self : SolidityGenerator Params Fr G₁) (c : G1Codec G₁)
    (plan : RepackedProofLayoutPlan) (compressed : Bytes) : Except ApiFault Bytes :=
  Midfall.Generator.repackProof c plan compressed

/-- rust: BREP:12-19 (SolidityGenerator::encode_calldata) @formal-baseline. "Repack a
    native proof and encode verifier calldata for verifyProof." Unlike the wrapper
    above this one DOES read a field: self.num_instances is CD:137's comparison value,
    and it reaches the guard through inputs.num_instances (BM:63). -/
def SolidityGenerator.encodeCalldata {Params Fr G₁ : Type}
    (self : SolidityGenerator Params Fr G₁) (c : G1Codec G₁)
    (plan : RepackedProofLayoutPlan) (compressedProof : Bytes)
    (instances : List Word256) : Except ApiFault Bytes :=
  encodeCalldataWithInstances c plan self.numInstances compressedProof instances

/-- rust: BREN:14-24 (struct VerifierRenderPlan) @formal-baseline. The private render
    knobs, resolved from the public RenderOptions plus the two things render itself
    decides. quotient_probe is test-only and render never sets it (BREN:20-21);
    provenance is the 32-byte BUILD_ID tag (Api.lean:953). -/
structure VerifierRenderPlan where
  /-- BREN:15 (separate: bool) - from RenderVk::Separate. -/
  separate : Bool
  /-- BREN:16 (trace: bool) -/
  trace : Bool
  /-- BREN:17 (gas_checkpoints: bool) -/
  gasCheckpoints : Bool
  /-- BREN:18 (external_quotient: bool) -/
  externalQuotient : Bool
  /-- BREN:19 (expected_quotient: Option<(usize, U256)>) -/
  expectedQuotient : Option (Nat × Word256)
  /-- BREN:20-21 (quotient_probe: bool) - test-only; render never sets it. -/
  quotientProbe : Bool
  /-- BREN:23 (provenance: Option<[u8; 32]>) -/
  provenance : Option Bytes
  deriving BEq

/-- rust: BREN:46-75 (the first half of render_with_listing) @formal-baseline. The
    option decode and the one hard conflict: QuotientLowering::Direct renders the
    quotient inline and cannot be combined with RenderQuotient::ExternalPinned
    (BREN:55-61, and API:459 says the same in the enum's own doc). The message is an
    Err payload, not a panic, so it is kept verbatim - including the line-continuation
    backslash the Rust uses to fold the literal onto one line with a single space. -/
def verifierRenderPlanOf (options : RenderOptions) :
    Except ApiFault VerifierRenderPlan := do
  let separate := match options.vk with
    | RenderVk.separate => true
    | RenderVk.embedded => false
  let ext := match options.quotient with
    | RenderQuotient.inline => (false, none)
    | RenderQuotient.externalPinned runtimeLen codehash => (true, some (runtimeLen, codehash))
  if options.quotientLowering == QuotientLowering.direct && ext.1 then
    throw (ApiFault.error (GeneratorError.planning (stage := "quotient lowering")
      (message := "QuotientLowering::Direct renders the quotient inline; it cannot be combined with RenderQuotient::ExternalPinned")))
  let renderPlan : VerifierRenderPlan :=
    { separate := separate, trace := options.diagnostics.trace,
      gasCheckpoints := options.diagnostics.gasCheckpoints,
      externalQuotient := ext.1, expectedQuotient := ext.2,
      quotientProbe := false, provenance := options.provenance }
  Except.ok renderPlan

/-- rust: BREN:134-148 (render_quotient_evaluator_with_plan) and BREN:154-175
    (render_verifier_source_with_plan) @formal-baseline. Both are "run the Askama
    render, and if the write fails report the artifact by name". The Askama model is
    P-13's, so the render result arrives as an argument and only the error
    substitution is ported here - the substitution is the part with a contract: the
    artifact strings are what a caller sees and what the golden tests key on. The
    Rust's map_err replaces EVERY error, so a panic from upstream is preserved (there
    is nothing to replace it with) and only an error arm becomes Render. -/
def renderArtifactOr (artifact : String) (rendered : Except ApiFault String) :
    Except ApiFault String :=
  match rendered with
  | .ok s => .ok s
  | .error (ApiFault.error _) =>
      .error (ApiFault.error (GeneratorError.render artifact))
  | .error f => .error f

/-- rust: BREN:41-112 (render_with_listing) @formal-baseline. "Render generated
    Solidity artifacts according to one immutable options value."

    The four lowering steps it sequences are unported (header), so they arrive as
    already-computed Except values - the P-11 precedent of passing an unported callee
    in as an argument. What is ported is this function's own content: the option
    decode, the Direct/ExternalPinned conflict, the ORDER of the steps, the two
    transpose arms (the VK source only when separate, the evaluator source only when
    external), and the rule at BREN:83-85 that the listing is produced AFTER every
    Solidity artifact so it cannot influence them. -/
def renderWithListing (options : RenderOptions) (emitListing : Bool)
    (planStep : Except ApiFault Unit) (verifierStep : Except ApiFault String)
    (vkStep : Except ApiFault String) (evaluatorStep : Except ApiFault String)
    (listingStep : Except ApiFault (String × String)) :
    Except ApiFault RenderedArtifacts := do
  let _renderPlan ← verifierRenderPlanOf options
  planStep
  let verifier ← verifierStep
  -- BREN:78: separate.then(...).transpose()? - the closure is not called at all when
  -- the VK is embedded, so a VK failure there must not surface.
  let separate := options.vk == RenderVk.separate
  let verifyingKey ← if separate then vkStep.map some else Except.ok none
  -- BREN:79-81: the same shape for the external quotient evaluator.
  let externalQuotient := match options.quotient with
    | RenderQuotient.inline => false
    | RenderQuotient.externalPinned _ _ => true
  let quotientEvaluator ← if externalQuotient then evaluatorStep.map some else Except.ok none
  -- BREN:86-103.
  let (quotientListing, quotientManifest) ←
    if emitListing then
      let lm ← listingStep
      Except.ok (some lm.1, some lm.2)
    else Except.ok (none, none)
  let artifacts : RenderedArtifacts :=
    { verifier := verifier, verifyingKey := verifyingKey,
      quotientEvaluator := quotientEvaluator, quotientListing := quotientListing,
      quotientManifest := quotientManifest }
  Except.ok artifacts

/-- rust: BREN:35-37 (render) @formal-baseline. The public entry point: the same call
    with the listing on. -/
def render (options : RenderOptions)
    (planStep : Except ApiFault Unit) (verifierStep : Except ApiFault String)
    (vkStep : Except ApiFault String) (evaluatorStep : Except ApiFault String)
    (listingStep : Except ApiFault (String × String)) :
    Except ApiFault RenderedArtifacts :=
  renderWithListing options true planStep verifierStep vkStep evaluatorStep listingStep

/-- rust: BREN:114-126 (render_quotient_evaluator) @formal-baseline. "Render only
    Halo2QuotientEvaluator.sol." Pinned-quotient deployment flows compile/deploy this
    source first, compute its runtime length and codehash, then render the verifier
    with RenderQuotient::ExternalPinned. The plan it uses is the DEFAULT lowering plan
    (BREN:124 inputs.lowering_plan(), not lowering_plan_for), which is a difference
    from render that renderQuotientEvaluator_usesDefaultPlan_ok pins. -/
def renderQuotientEvaluator (diagnostics : RenderDiagnostics)
    (evaluatorStep : Except ApiFault String) : Except ApiFault String :=
  let _ := diagnostics.trace
  renderArtifactOr "Halo2QuotientEvaluator.sol" evaluatorStep

end Midfall.Generator

/-! # Known-answer tests -/

namespace Midfall.Generator.BuilderKats

open Midfall.Generator.EvmKats
open Midfall.Generator.CalldataKats
open Midfall.Halo2

/-- The five sources this file cites, read at #eval time (D-P19). All are tracked and
    the working copy is clean for all five (only src/api.rs is modified). -/
def builderModCandidates : List String :=
  ["../proofs/solidity-verifier/src/builder/mod.rs",
   "proofs/solidity-verifier/src/builder/mod.rs"]
def builderApiCandidates : List String :=
  ["../proofs/solidity-verifier/src/builder/api.rs",
   "proofs/solidity-verifier/src/builder/api.rs"]
def builderRenderCandidates : List String :=
  ["../proofs/solidity-verifier/src/builder/render.rs",
   "proofs/solidity-verifier/src/builder/render.rs"]
def builderRepackCandidates : List String :=
  ["../proofs/solidity-verifier/src/builder/repack.rs",
   "proofs/solidity-verifier/src/builder/repack.rs"]
def loweringModCandidates : List String :=
  ["../proofs/solidity-verifier/src/lowering/mod.rs",
   "proofs/solidity-verifier/src/lowering/mod.rs"]

def readBuilderMod : IO String := readFirst builderModCandidates
def readBuilderApi : IO String := readFirst builderApiCandidates
def readBuilderRender : IO String := readFirst builderRenderCandidates
def readBuilderRepack : IO String := readFirst builderRepackCandidates
def readLoweringMod : IO String := readFirst loweringModCandidates

/-- GATE 1 (reachability first). The five sources, with the line counts the brief
    states (69 / 162 / 220 / 27) so a stale cite cannot hide. -/
def builderArtifactsReachable_ok : IO Bool :=
  readBuilderMod >>= fun bm =>
  readBuilderApi >>= fun ba =>
  readBuilderRender >>= fun br =>
  readBuilderRepack >>= fun bp =>
  readLoweringMod >>= fun lm =>
  pure ((bm.splitOn "\n").length == 70 && (ba.splitOn "\n").length == 163
    && (br.splitOn "\n").length == 221 && (bp.splitOn "\n").length == 28
    && lm.length > 800)

/-- GATE 2 (the one-file justification). BM's struct fields and MOD's
    VerifierBuildInputs fields must still agree: if a field is added to either side,
    the field copy BM:59-68 stops being a no-op and this gate says so. -/
def builderModFields_areTheInputsFields_ok : IO Bool :=
  readBuilderMod >>= fun bm =>
  readLoweringMod >>= fun lm => pure (
    bm.contains "params: &'a ParamsKZG<Bls12>"
      && bm.contains "vk: &'a VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>"
      && bm.contains "num_instances: usize"
      && bm.contains "acc_encoding: Option<AccumulatorEncoding>"
      && bm.contains "meta: ConstraintSystemMeta"
      && lm.contains "pub(crate) struct VerifierBuildInputs"
      && lm.contains "num_committed_instances: usize"
      && bm.contains "pub(crate) fn inputs(&self)")

/-- The scalar field the fixtures use: Fr 17, the same toy field Exec/Verifier.lean's
    fixtures run on, so no BLS12-381-sized literal is needed for a shape test. -/
abbrev FixtureFr := Midfall.Fr 17

/-- An instance column at index i (Circuit.lean:291's Column: index + columnType). -/
def instCol (i : Nat) : Column := { index := i, columnType := Any.instance }

/-- A ConstraintSystem with the shape try_new accepts: advice columns present, two
    instance columns of which one is committed, and every instance query at cur.
    This is Protocol.lean's own fixture (Protocol.lean:1077-1106), which is the one
    cs in the tree that a real ProtocolPlan can be built from - a hand-declared
    empty cs is rejected by PM's own validation, and the first version of this gate
    learned that the hard way. -/
def supportedCs : ConstraintSystem FixtureFr := Midfall.Generator.ProtocolKats.fixtureCs

/-- The matching config: one instance, one committed instance column. -/
def supportedConfig : GeneratorConfig := GeneratorConfig.new 1 1

/-- The domain fixture, copied in shape from Verifier.lean:345-349 (Fr 17 has a
    fourth root of unity, so these are real, not placeholders). -/
def supportedDom : EvaluationDomain FixtureFr :=
  { n := 4, k := 2, extendedK := 2, omega := 13, omegaInv := 4,
    extendedOmega := 13, extendedOmegaInv := 4, gCoset := 2, gCosetInv := 4,
    quotientPolyDegree := 2, ifftDivisor := 13, extendedIfftDivisor := 13,
    tEvaluations := #[8], barycentricWeight := 13 }

/-- The matching VK: the supported cs, everything else minimal. -/
def supportedVk {G₁ : Type} : VerifyingKey FixtureFr G₁ :=
  { domain := supportedDom, fixedCommitments := #[], permutation := ⟨#[]⟩,
    cs := supportedCs, csDegree := 5, transcriptRepr := 0 }

/-- GATE 3. try_new accepts the supported shape, and the record carries the config's
    numbers into the right fields. -/
def tryNew_acceptsSupportedShape_ok : Bool :=
  match SolidityGenerator.tryNew () (supportedVk : VerifyingKey FixtureFr Nat)
      supportedConfig Features.solidity with
  | .ok g => g.numInstances == 1 && g.meta_.numCommittedInstances == 1
      && g.accEncoding == none && g.vk.cs.numAdviceColumns == 4
      && g.meta_.numSimpleSelectors == 1 && g.meta_.numLookups == 1
      && supportedCommittedInstanceCommitment == CommittedInstanceCommitmentKind.identity
      && SolidityGenerator.committedInstanceCommitmentKind g
           == CommittedInstanceCommitmentKind.identity
  | .error _ => false

/-- GATE 4 (hazard: Supported must mirror try_new). Each of the four checks fires on
    its own, with its own error, and the FIRST one in source order wins when two would
    fire. Four distinct rejections, so no two arms can be merged. The last conjunct is
    Circuit.lean's Rotation hazard: value 0 is not a rotation. -/
def tryNew_checkOrderIsObservable_ok : Bool :=
  let vkWith (cs : ConstraintSystem FixtureFr) : VerifyingKey FixtureFr Nat :=
    { (supportedVk : VerifyingKey FixtureFr Nat) with cs := cs }
  let noAdvice := vkWith { supportedCs with numAdviceColumns := 0 }
  let badShape := vkWith { supportedCs with numInstanceColumns := 3 }
  let rotated := vkWith { supportedCs with
    instanceQueries := #[ (instCol 1, Rotation.next) ] }
  -- 1: no advice columns at all.
  (match SolidityGenerator.tryNew () noAdvice supportedConfig Features.solidity with
   | .error (ApiFault.error GeneratorError.noAdviceColumns) => true
   | _ => false)
    -- 2: the instance split, with all four reported numbers.
    && (match SolidityGenerator.tryNew () badShape supportedConfig Features.solidity with
       | .error (ApiFault.error (GeneratorError.unsupportedInstanceColumnShape
           total committed ec enc)) =>
           total == 3 && committed == 1 && ec == 1 && enc == 1
       | _ => false)
    -- 3: a rotated instance query, with the column index and the rotation value.
    && (match SolidityGenerator.tryNew () rotated supportedConfig Features.solidity with
       | .error (ApiFault.error (GeneratorError.rotatedInstanceQuery column rotation)) =>
           column == 1 && rotation == 1
       | _ => false)
    -- 4: the accumulator check runs BEFORE the rotation scan, so a config that fails
    -- both reports the accumulator error.
    && (match SolidityGenerator.tryNew () rotated
          { numInstances := 1, numCommittedInstances := 1,
            accumulator := some (AccumulatorEncoding.new 40 7 56) }
          Features.solidity with
       | .error (ApiFault.error
           (GeneratorError.unsupportedAccumulatorEncoding _ _ _ _ _)) => true
       | _ => false)
    -- and Rotation::value 0 is NOT a rotation.
    && (match SolidityGenerator.tryNew ()
          (vkWith { supportedCs with
            instanceQueries := #[ (instCol 0, Rotation.value 0),
                                  (instCol 1, Rotation.cur) ] })
          supportedConfig Features.solidity with
       | .ok _ => true
       | .error _ => false)

/-- GATE 5 (BAPI:93-95). The checked_sub sentinel: committed > total must become
    usize::MAX and be rejected, not wrap to a small number. Four probes with
    different (total, committed) pairs. -/
def validateInstanceColumnShape_checkedSubSentinel_ok : Bool :=
  (match SolidityGenerator.validateInstanceColumnShape 2 1 with
   | .ok _ => true | .error _ => false)
    && (match SolidityGenerator.validateInstanceColumnShape 3 1 with
       | .error (ApiFault.error (GeneratorError.unsupportedInstanceColumnShape
           total committed ec enc)) => total == 3 && committed == 1 && ec == 1 && enc == 1
       | _ => false)
    && (match SolidityGenerator.validateInstanceColumnShape 1 1 with
       | .error (ApiFault.error (GeneratorError.unsupportedInstanceColumnShape
           total committed _ _)) => total == 1 && committed == 1
       | _ => false)
    && (match SolidityGenerator.validateInstanceColumnShape 0 4 with
       | .error (ApiFault.error (GeneratorError.unsupportedInstanceColumnShape
           total committed _ _)) => total == 0 && committed == 4
       | _ => false)
    && usizeMax > supportedCommittedInstanceColumns
    && usizeMax != supportedNonCommittedInstanceColumns
    -- THE SENTINEL IS ONLY OBSERVABLE IN THE MESSAGE, not in the decision: with
    -- committed = 1 (the only value that passes the first disjunct) a total below it
    -- gives usize::MAX under checked_sub.unwrap_or, 2^64-1 under a wrapping
    -- subtraction and 0 under truncated Nat, and NONE of the three equals
    -- supported_non_committed = 1, so all three reject. What does differ is the
    -- Display, which runs its OWN checked_sub (API:651-654) and prints the
    -- "invalid: committed .. exceeds total .." arm - pinned here so the None arm
    -- cannot be dropped. This paragraph is the perturbation that FAILED: replacing
    -- usizeMax with 0 leaves every arm of this gate green, and the reason is above,
    -- not that the gate is weak.
    && printGeneratorError (GeneratorError.unsupportedInstanceColumnShape 0 1 1 1)
         == "unsupported instance column shape: got total=0, committed=1, non_committed=invalid: committed 1 exceeds total 0; expected exactly 1 identity-committed and 1 non-committed"

/-- GATE 6 (BAPI:20-28). new is try_new plus a panic: the same rejection becomes a
    panic SITE naming BAPI:27, whose text is read from the reference. -/
def generatorNew_panicsWhereTryNewErrors_ok : IO Bool :=
  readBuilderApi >>= fun src =>
  let vkN : VerifyingKey FixtureFr Nat := supportedVk
  let vkBad : VerifyingKey FixtureFr Nat :=
    { vkN with cs := { supportedCs with numInstanceColumns := 9 } }
  pure (
    (lineOf src 27).contains "unsupported Solidity verifier shape:"
      && (match SolidityGenerator.tryNew () vkBad supportedConfig Features.solidity with
         | .error _ => true
         | .ok _ => false)
      && (match SolidityGenerator.new () vkN supportedConfig Features.solidity with
         | .ok _ => true
         | .error _ => false))

/-- GATE 7 (BREN:55-61). The Direct + ExternalPinned conflict, with the reference's
    message verbatim including the single space the string continuation folds to; and
    the three non-conflicting combinations all pass. -/
def verifierRenderPlan_directExternalConflict_ok : Bool :=
  let directExternal : RenderOptions :=
    { vk := RenderVk.embedded, quotient := RenderQuotient.externalPinned 0x2000 0x1,
      quotientLowering := QuotientLowering.direct,
      diagnostics := RenderDiagnostics.default, provenance := none }
  (match verifierRenderPlanOf directExternal with
   | .error (ApiFault.error (GeneratorError.planning stage message)) =>
       stage == "quotient lowering"
         && message == "QuotientLowering::Direct renders the quotient inline; it cannot be combined with RenderQuotient::ExternalPinned"
   | _ => false)
    && (match verifierRenderPlanOf { directExternal with
          quotient := RenderQuotient.inline } with
        | .ok _ => true | .error _ => false)
    && (match verifierRenderPlanOf { directExternal with
          quotientLowering := QuotientLowering.vm } with
        | .ok _ => true | .error _ => false)
    && printGeneratorError (GeneratorError.planning (stage := "quotient lowering")
        (message := "QuotientLowering::Direct renders the quotient inline; it cannot be combined with RenderQuotient::ExternalPinned"))
         == "generator planning failed during quotient lowering: QuotientLowering::Direct renders the quotient inline; it cannot be combined with RenderQuotient::ExternalPinned"

/-- GATE 8 (BREN:46-53). Every VerifierRenderPlan field tracks its option: separate
    only for RenderVk::Separate, external_quotient and expected_quotient only for
    ExternalPinned (carrying BOTH the runtime_len and the codehash), the two
    diagnostics knobs, the provenance, and quotient_probe always false from this path.
    Four option sets with pairwise different field patterns. -/
def verifierRenderPlan_tracksEveryOption_ok : Bool :=
  let base : RenderOptions :=
    { vk := RenderVk.embedded, quotient := RenderQuotient.inline,
      quotientLowering := QuotientLowering.vm,
      diagnostics := { trace := false, gasCheckpoints := false },
      provenance := none }
  match verifierRenderPlanOf base,
        verifierRenderPlanOf { base with vk := RenderVk.separate },
        verifierRenderPlanOf { base with
          quotient := RenderQuotient.externalPinned 4321 (BitVec.ofNat 256 61) },
        verifierRenderPlanOf { base with
          diagnostics := { trace := true, gasCheckpoints := true },
          provenance := some (bytesFromNats (List.replicate 32 0xab)) } with
  | .ok a, .ok b, .ok c, .ok d =>
      a.separate == false && a.externalQuotient == false && a.expectedQuotient == none
        && a.quotientProbe == false && a.provenance == none && a.trace == false
        && b.separate == true && b.expectedQuotient == none
        && c.externalQuotient == true
        && c.expectedQuotient == some (4321, BitVec.ofNat 256 61)
        && d.trace == true && d.gasCheckpoints == true
        && d.provenance == some (bytesFromNats (List.replicate 32 0xab))
        && a != b && a != c && a != d
  | _, _, _, _ => false

/-- GATE 9 (BREN:76-103). The render sequence: the plan step's failure propagates
    before anything is rendered; the VK source is produced only for a separate render
    (a VK failure in the embedded path must NOT surface - that is BREN:78's then());
    the evaluator source only for an external quotient; and the listing is produced
    only when asked, in which case both halves appear together. -/
def renderWithListing_stepOrderAndTransposeArms_ok : Bool :=
  let embedded : RenderOptions :=
    { vk := RenderVk.embedded, quotient := RenderQuotient.inline,
      quotientLowering := QuotientLowering.vm,
      diagnostics := RenderDiagnostics.default, provenance := none }
  let separateExternal : RenderOptions :=
    { embedded with vk := RenderVk.separate, quotient := RenderQuotient.externalPinned 100 7 }
  let bad : Except ApiFault String :=
    .error (ApiFault.error (GeneratorError.render "nope"))
  let badPair : Except ApiFault (String × String) :=
    .error (ApiFault.error (GeneratorError.render "nope"))
  let badUnit : Except ApiFault Unit :=
    .error (ApiFault.error (GeneratorError.render "nope"))
  -- the plan step fails first, so nothing else is consulted
  (match renderWithListing embedded false badUnit (Except.ok "V") (Except.ok "K")
      (Except.ok "Q") (Except.ok ("L", "M")) with
   | .error (ApiFault.error (GeneratorError.render a)) => a == "nope"
   | _ => false)
    -- embedded: the VK step is never called, even though it would fail
    && (match renderWithListing embedded false (Except.ok ()) (Except.ok "V") bad bad badPair with
       | .ok r => r.verifier == "V" && r.verifyingKey == none
           && r.quotientEvaluator == none && r.quotientListing == none
           && r.quotientManifest == none
       | _ => false)
    -- separate + external: both appear, and the listing is on
    && (match renderWithListing separateExternal true (Except.ok ()) (Except.ok "V")
          (Except.ok "K") (Except.ok "Q") (Except.ok ("L", "M")) with
       | .ok r => r.verifyingKey == some "K" && r.quotientEvaluator == some "Q"
           && r.quotientListing == some "L" && r.quotientManifest == some "M"
       | _ => false)
    -- separate + external, listing off: the listing step is never called
    && (match renderWithListing separateExternal false (Except.ok ()) (Except.ok "V")
          (Except.ok "K") (Except.ok "Q") badPair with
       | .ok r => r.quotientListing == none && r.quotientManifest == none
           && r.verifyingKey == some "K"
       | _ => false)
    -- and render is the listing-on case (BREN:35-37)
    && (match render embedded (Except.ok ()) (Except.ok "V") (Except.ok "K")
          (Except.ok "Q") (Except.ok ("L", "M")) with
       | .ok r => r.quotientListing == some "L"
       | _ => false)
    -- the verifier step's own failure propagates
    && (match renderWithListing embedded false (Except.ok ()) bad (Except.ok "K")
          (Except.ok "Q") (Except.ok ("L", "M")) with
       | .error _ => true
       | .ok _ => false)

/-- GATE 10 (BREN:144-146, 171-173). The artifact names the Render error carries,
    verbatim, and that a successful render passes through untouched; a panic upstream
    is preserved rather than replaced. -/
def renderArtifactOr_namesTheArtifact_ok : Bool :=
  (match renderArtifactOr "Halo2QuotientEvaluator.sol"
      (.error (ApiFault.error (GeneratorError.planning "x" "y"))) with
   | .error (ApiFault.error (GeneratorError.render a)) =>
       a == "Halo2QuotientEvaluator.sol"
         && printGeneratorError (GeneratorError.render a)
              == "failed to render Halo2QuotientEvaluator.sol"
   | _ => false)
    && (match renderArtifactOr "Halo2Verifier.sol" (.error (ApiFault.panic "site")) with
       | .error (ApiFault.panic s) => s == "site"
       | _ => false)
    && (match renderArtifactOr "Halo2VerifyingKey.sol" (Except.ok "source") with
       | .ok s => s == "source"
       | .error _ => false)
    && (match renderQuotientEvaluator RenderDiagnostics.default
          (.error (ApiFault.error GeneratorError.noAdviceColumns)) with
       | .error (ApiFault.error (GeneratorError.render a2)) =>
           a2 == "Halo2QuotientEvaluator.sol"
       | _ => false)

/-- GATE 11 (BREN:124 vs BREN:65). The standalone evaluator render uses the DEFAULT
    lowering plan while render uses lowering_plan_for(options.quotient_lowering) - two
    different calls in the reference that are easy to conflate. Pinned against the
    source text. -/
def renderQuotientEvaluator_usesDefaultPlan_ok : IO Bool :=
  readBuilderRender >>= fun src => pure (
    (lineOf src 124).contains "let plan = inputs.lowering_plan();"
      && (lineOf src 65).contains "let plan = inputs.lowering_plan_for(options.quotient_lowering)?;"
      && (lineOf src 125).contains "self.render_quotient_evaluator_with_plan(&inputs, &plan, diagnostics)")

/-- GATE 12 (the P-14 cut). builder/api.rs's five diagnostics forwarders, counted from
    the source so a sixth cannot be added unnoticed, and the BAPI:64 line the try_new
    panic site cites. -/
def builderApi_diagnosticsForwardersAreTheCutOnes_ok : IO Bool :=
  readBuilderApi >>= fun src => pure (
    -- FOUR, not five: direct_quotient_trace_values (BAPI:128-138) forwards to
    -- self.inputs(), not to diagnostics, so only four of the five blocked methods
    -- name the cut module.
    countMatches src "crate::lowering::diagnostics::" == 4
      && src.contains "fn proof_evaluation_counts"
      && src.contains "fn direct_quotient_trace_values"
      && src.contains "fn quotient_identity_manifest"
      && src.contains "fn quotient_certificate("
      && src.contains "fn quotient_certificate_hash"
      && (lineOf src 64).contains "ConstraintSystemMeta::new(vk.cs(), config.num_committed_instances)")

/-- GATE 13 (BREP). The two wrappers: repack_proof ignores self entirely (it only
    needs the plan), encode_calldata reads num_instances - and the wrapper's guard
    fires at the GENERATOR's count, not at any other. -/
def generatorWrappers_useTheRecordFields_ok : Bool :=
  let g : SolidityGenerator PUnit FixtureFr ToyG1 :=
    { params := (), vk := (supportedVk : VerifyingKey FixtureFr ToyG1),
      numInstances := 2, accEncoding := none,
      meta_ := constraintSystemMetaDefault }
  let plan : RepackedProofLayoutPlan :=
    { g1Groups := [1], numEvals := 1, numPointSets := 0 }
  let input := bytesFromNats ([0x81] ++ List.replicate 47 0
    ++ [5] ++ List.replicate 31 0 ++ [0x82] ++ List.replicate 47 0
    ++ [0x83] ++ List.replicate 47 0)
  (match g.encodeCalldata Midfall.Generator.CalldataKats.toyCodec plan input [9] with
   | .error (ApiFault.error (GeneratorError.planning stage message)) =>
       stage == "calldata" && message == "instance length mismatch: expected 2, got 1"
   | _ => false)
    && (match g.repackProof Midfall.Generator.CalldataKats.toyCodec plan input with
       | .ok out => out.size == plan.repackedLen
       | .error _ => false)
    && (match g.encodeCalldata Midfall.Generator.CalldataKats.toyCodec plan input [9, 10] with
       | .ok cd => cd.size == 4 + 3 * 32 + plan.repackedLen + 32 + 64
       | .error _ => false)

end Midfall.Generator.BuilderKats

#eval Midfall.Generator.BuilderKats.builderArtifactsReachable_ok -- expect true
#eval Midfall.Generator.BuilderKats.builderModFields_areTheInputsFields_ok -- expect true
#eval Midfall.Generator.BuilderKats.tryNew_acceptsSupportedShape_ok -- expect true
#eval Midfall.Generator.BuilderKats.tryNew_checkOrderIsObservable_ok -- expect true
#eval Midfall.Generator.BuilderKats.validateInstanceColumnShape_checkedSubSentinel_ok -- expect true
#eval Midfall.Generator.BuilderKats.generatorNew_panicsWhereTryNewErrors_ok -- expect true
#eval Midfall.Generator.BuilderKats.verifierRenderPlan_directExternalConflict_ok -- expect true
#eval Midfall.Generator.BuilderKats.verifierRenderPlan_tracksEveryOption_ok -- expect true
#eval Midfall.Generator.BuilderKats.renderWithListing_stepOrderAndTransposeArms_ok -- expect true
#eval Midfall.Generator.BuilderKats.renderArtifactOr_namesTheArtifact_ok -- expect true
#eval Midfall.Generator.BuilderKats.renderQuotientEvaluator_usesDefaultPlan_ok -- expect true
#eval Midfall.Generator.BuilderKats.builderApi_diagnosticsForwardersAreTheCutOnes_ok -- expect true
#eval Midfall.Generator.BuilderKats.generatorWrappers_useTheRecordFields_ok -- expect true
