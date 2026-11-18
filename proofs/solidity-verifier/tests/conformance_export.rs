//! P-C3: the Phase 3 conformance **exporter** (plan Section 5, docs/conformance-schema.md).
//!
//! Adds no verifier logic. It runs the *existing* native verifier pipeline on the
//! poseidon fixture and writes a canonical bundle that the Lean runner
//! (`lake exe midfall-conformance`) replays:
//!
//! ```text
//!   vk.json  params.json  instances.json  proof.bin  trace.json
//! ```
//!
//! Output directory: `$MIDFALL_CONFORMANCE_OUT`, defaulting to
//! `<repo>/formal/fixtures/conformance/poseidon`. Nothing under
//! `proofs/solidity-verifier/fixtures/` is written; the committed fixture is only
//! *compared against*, see below.
//!
//! WHY A WRAPPER TRANSCRIPT RATHER THAN MORE TRACE HOOKS. docs/conformance-schema.md
//! needs two things the existing `solidity_trace` does not carry: the **raw digest**
//! at every squeeze (the trace stores only `digest mod r`, which is not invertible,
//! so the chain cannot be reseeded from it - docs/ecosystem.md section 11) and the
//! **absorb prefix** (vk_repr, the committed instance, the instance lengths and
//! values - also section 11). Adding either inside `proofs/src` would be a baseline
//! change, which the brief forbids. Instead this file defines `Recording`, a
//! `Transcript` implementation that *delegates* every operation to
//! `CircuitTranscript<Keccak256>` and logs what it saw. The schedule is therefore
//! still the verifier's own: there is no second copy of the read order here, which
//! is the failure mode docs/REVIEW.md R-30 / R-32 record.
//!
//! WHY THE REGENERATED FIXTURE. `rust_trace.json`, `proof.bin`, `vk.bin` and
//! `instance.be` under `fixtures/poseidon/` are the committed reference. This test
//! rebuilds the same circuit the same way `tests/poseidon_fixture.rs` does
//! (`PoseidonExample` at k=6, witness from `ChaCha8Rng::seed_from_u64(42)`, proof
//! RNG seeded `0xdebd`) and then *reports* whether the bytes it produced equal the
//! committed ones. It does not fail on a mismatch, because a mismatch there is a
//! fixture-provenance question, not a harness question; the answer is recorded in
//! `trace.json` under `fixture_match` and printed.

#![cfg(feature = "rust-verifier-trace")]

use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use ff::{Field, PrimeField};
use group::{Curve, Group};
use halo2_solidity_verifier::{GeneratorConfig, SolidityGenerator, __test_only_g2_to_u256s};
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
};
use midnight_curves::{Bls12, Fq, G1Affine, G1Projective};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{prepare, solidity_trace, Any, Error, Expression, VerifyingKey},
    poly::{
        kzg::{msm::msm_specific, KZGCommitmentScheme},
        CommitmentLabel,
    },
    transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use serde_json::json;
use sha2::Sha256;
use sha3::{Digest, Keccak256};

type F = Fq;
type Vk = VerifyingKey<F, KZGCommitmentScheme<Bls12>>;
type Params = midnight_proofs::poly::kzg::params::ParamsKZG<Bls12>;

const K: u32 = 6;
const NUM_COMMITTED_INSTANCES: usize = 1;

// ---------------------------------------------------------------------------
// The circuit: identical to tests/poseidon_fixture.rs
// ---------------------------------------------------------------------------

#[derive(Clone, Default)]
struct PoseidonExample;

impl Relation for PoseidonExample {
    type Instance = F;
    type Witness = [F; 3];

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned_message = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.poseidon(layouter, &assigned_message)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch { poseidon: true, ..ZkStdLibArch::default() }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonExample)
    }
}

// ---------------------------------------------------------------------------
// Recording: a Transcript that delegates and logs
// ---------------------------------------------------------------------------

/// One entry of the transcript log. `Absorb` is an explicit `common()` by the
/// verifier (the prefix); `Read` is a proof-stream read (wire bytes plus the bytes
/// the transcript actually absorbed); `Squeeze` carries the raw digest and, once the
/// run has finished and the trace events have been aligned, the challenge the
/// verifier received under a name.
// The unused fields are kept: they are what `Debug` prints when an export is
// diagnosed by hand, and dropping them would make the log less legible.
#[allow(dead_code)]
#[derive(Clone, Debug)]
enum Ev {
    Absorb { tag: String, bytes: Vec<u8> },
    Read { tag: String, name: String, wire: Vec<u8>, absorbed: Vec<u8> },
    Squeeze { digest: Vec<u8>, name: Option<String>, challenge: Option<Vec<u8>> },
}

#[derive(Clone, Debug)]
struct Recording {
    inner: CircuitTranscript<Keccak256>,
    /// The exact byte string the delegated hasher has absorbed since the last
    /// squeeze. implementors.rs:198-212 reseeds with the digest, so this shadow
    /// reproduces the state without touching the private hasher.
    shadow: Vec<u8>,
    events: Vec<Ev>,
    n_absorb: usize,
    n_read: usize,
}

impl Recording {
    fn new(bytes: &[u8]) -> Self {
        Recording {
            inner: CircuitTranscript::<Keccak256>::init_from_bytes(bytes),
            shadow: Vec::new(),
            events: Vec::new(),
            n_absorb: 0,
            n_read: 0,
        }
    }

    fn squeeze_count(&self) -> usize {
        self.events.iter().filter(|e| matches!(e, Ev::Squeeze { .. })).count()
    }
}

impl Transcript for Recording {
    type Hash = Keccak256;

    fn init() -> Self {
        Recording::new(&[])
    }

    fn init_from_bytes(bytes: &[u8]) -> Self {
        Recording::new(bytes)
    }

    fn squeeze_challenge<T: Sampleable<Keccak256>>(&mut self) -> T {
        // The digest of everything absorbed so far, computed here rather than
        // inside proofs/src. Sampleable for Fq (implementors.rs:341-345) is
        // BigUint::from_bytes_be(digest) mod r, so challenge = digest mod r
        // except where the verifier truncates after sampling (x3).
        let digest = Keccak256::new().chain_update(&self.shadow).finalize().to_vec();
        let value = self.inner.squeeze_challenge::<T>();
        self.shadow = digest.clone();
        self.events.push(Ev::Squeeze { digest, name: None, challenge: None });
        value
    }

    fn common<T: Hashable<Keccak256>>(&mut self, input: &T) -> io::Result<()> {
        let bytes = input.to_input();
        self.inner.common(input)?;
        self.shadow.extend_from_slice(&bytes);
        self.events.push(Ev::Absorb { tag: format!("absorb[{}]", self.n_absorb), bytes });
        self.n_absorb += 1;
        Ok(())
    }

    fn read<T: Hashable<Keccak256>>(&mut self) -> io::Result<T> {
        let before = self.inner.buffer().position() as usize;
        let value: T = self.inner.read()?;
        let after = self.inner.buffer().position() as usize;
        let wire = self.inner.buffer().get_ref()[before..after].to_vec();
        let absorbed = value.to_input();
        self.shadow.extend_from_slice(&absorbed);
        self.events.push(Ev::Read {
            tag: format!("read[{}]", self.n_read),
            name: String::new(),
            wire,
            absorbed,
        });
        self.n_read += 1;
        Ok(value)
    }

    fn write<T: Hashable<Keccak256>>(&mut self, input: &T) -> io::Result<()> {
        // The verifier never writes; keep the absorb semantics and do not grow the
        // proof buffer, so a stray write shows up as a length mismatch downstream.
        self.common(input)
    }

    fn finalize(self) -> Vec<u8> {
        self.inner.finalize()
    }

    fn assert_empty(&mut self) -> io::Result<()> {
        self.inner.assert_empty()
    }
}

// ---------------------------------------------------------------------------
// Encoding helpers
// ---------------------------------------------------------------------------

fn be_hex(x: &F) -> String {
    hex::encode(<F as Hashable<Keccak256>>::to_input(x))
}

fn point_hex(p: &G1Projective) -> String {
    hex::encode(<G1Projective as Hashable<Keccak256>>::to_bytes(p))
}

fn g2_hex(p: &midnight_curves::G2Projective) -> String {
    use group::GroupEncoding;
    hex::encode(p.to_affine().to_bytes().as_ref())
}

/// F.1: one `Expression<F>` as data, so the constraint system's gate / lookup /
/// trashcan polynomials reach the Lean tree as FACTS instead of as a port of the
/// builder that made them.
///
/// The variant set mirrors `proofs/src/plonk/circuit.rs:824-849` one for one and
/// every payload is read through a PUBLIC accessor (`FixedQuery::column_index`,
/// `AdviceQuery::phase`, `Challenge::index`, ...); nothing here reaches into a
/// `pub(crate)` field, so this adds no baseline surface. `degree` is carried on
/// every node because it is the only thing the plan path actually reads of an
/// expression (`ConstraintSystem::degree`, `BatchedArgument::num_chunks`,
/// `TrashArgument::required_degree`), and shipping the reference's own value lets
/// the importer KAT its port of `Expression::degree` against the artifact rather
/// than trusting its own tree walk.
fn expr_json(e: &Expression<F>) -> serde_json::Value {
    let deg = e.degree();
    match e {
        Expression::Constant(c) => json!({"k": "constant", "f": be_hex(c), "degree": deg}),
        Expression::Selector(s) => json!({
            "k": "selector", "index": s.index(), "is_simple": s.is_simple(), "degree": deg
        }),
        Expression::Fixed(q) => json!({
            "k": "fixed", "index": q.index(), "col": q.column_index(),
            "rot": q.rotation().0, "degree": deg
        }),
        Expression::Advice(q) => json!({
            "k": "advice", "index": q.index, "col": q.column_index(),
            "rot": q.rotation().0, "phase": q.phase(), "degree": deg
        }),
        Expression::Instance(q) => json!({
            "k": "instance", "index": q.index, "col": q.column_index(),
            "rot": q.rotation().0, "degree": deg
        }),
        Expression::Challenge(c) => json!({
            "k": "challenge", "index": c.index(), "phase": c.phase(), "degree": deg
        }),
        Expression::Negated(a) => json!({"k": "negated", "a": expr_json(a), "degree": deg}),
        Expression::Sum(a, b) => json!({
            "k": "sum", "a": expr_json(a), "b": expr_json(b), "degree": deg
        }),
        Expression::Product(a, b) => json!({
            "k": "product", "a": expr_json(a), "b": expr_json(b), "degree": deg
        }),
        Expression::Scaled(a, s) => json!({
            "k": "scaled", "a": expr_json(a), "f": be_hex(s), "degree": deg
        }),
    }
}

/// Trace ids the verifier records for squeezed challenges: 7 theta, 8 beta,
/// 9 gamma, 10 y, 11 x, 12 trash_challenge, 13 x1, 14 x2, 15 x3, 16 x4, and
/// USER_CHALLENGE_TRACE_BASE + i for the cs challenges (none for poseidon).
fn is_challenge_id(id: u64) -> bool {
    (7..=16).contains(&id)
        || (solidity_trace::USER_CHALLENGE_TRACE_BASE
            ..solidity_trace::USER_CHALLENGE_TRACE_BASE + 1000)
                .contains(&id)
}

fn is_proof_read_id(id: u64) -> bool {
    (solidity_trace::PROOF_COMMITMENT_TRACE_BASE..solidity_trace::PROOF_COMMITMENT_TRACE_BASE + 10_000)
        .contains(&id)
        || (solidity_trace::PROOF_EVAL_TRACE_BASE..solidity_trace::PROOF_EVAL_TRACE_BASE + 10_000)
            .contains(&id)
}

// ---------------------------------------------------------------------------
// REF.11: which SRS the bundle is generated under
// ---------------------------------------------------------------------------

/// The SRS selector, MIDFALL_CONFORMANCE_SRS.
///
/// * unset, or 'filecoin' - the production Filecoin ceremony SRS that
///   'srs_for_test' loads from $SRS_DIR. This is **F0**, the bundle already
///   committed at 'formal/fixtures/conformance/poseidon/'. Its trapdoor is
///   unknown, so the Lean side can replay acceptance but cannot *compute* it.
/// * 'unsafe:<seed>' - a seeded test SRS, ParamsKZG::unsafe_setup(K,
///   ChaCha8Rng::seed_from_u64(seed)) (proofs/src/poly/kzg/params.rs:98-135).
///   The trapdoor is re-derived from the same seed and exported into
///   'params.json', which is what D-P63 approves and what turns both the
///   reference gate and the acceptance gate into computations. This is **F1**,
///   written to 'formal/fixtures/conformance/poseidon-testsrs/'.
///
/// **The trapdoor is public.** D-P63: no soundness of the proof system is
/// claimed for F1; SrsEncodes is not a hypothesis of Done.
enum SrsMode {
    Filecoin,
    Unsafe { seed: u64 },
}

impl SrsMode {
    fn from_env() -> Self {
        let raw = match env::var("MIDFALL_CONFORMANCE_SRS") {
            Err(_) => return SrsMode::Filecoin,
            Ok(v) => v,
        };
        if raw.is_empty() || raw == "filecoin" {
            return SrsMode::Filecoin;
        }
        let rest = raw.strip_prefix("unsafe:").ok_or_else(|| raw.clone()).and_then(|rest| {
            parse_seed(rest).map(|seed| SrsMode::Unsafe { seed }).ok_or_else(|| {
                format!("not a u64 seed (decimal or 0x-hex): {rest}")
            })
        });
        match rest {
            Ok(m) => m,
            Err(why) => panic!("MIDFALL_CONFORMANCE_SRS must be empty, 'filecoin', or \
                                'unsafe:<seed>'; got {raw:?} ({why})"),
        }
    }

    fn kind(&self) -> &'static str {
        match self {
            SrsMode::Filecoin => "filecoin",
            SrsMode::Unsafe { .. } => "unsafe-seeded",
        }
    }

    fn seed(&self) -> Option<u64> {
        match self {
            SrsMode::Filecoin => None,
            SrsMode::Unsafe { seed } => Some(*seed),
        }
    }

    /// The bundle directory this mode owns. F0 and F1 are separate directories,
    /// so generating F1 can never touch the committed Filecoin bundle.
    fn default_dir(&self) -> PathBuf {
        let leaf = match self {
            SrsMode::Filecoin => "poseidon",
            SrsMode::Unsafe { .. } => "poseidon-testsrs",
        };
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../formal/fixtures/conformance")
            .join(leaf)
    }
}

fn parse_seed(s: &str) -> Option<u64> {
    if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        u64::from_str_radix(h, 16).ok()
    } else {
        s.parse::<u64>().ok()
    }
}

/// sha256 of a byte string, lowercase hex. Used for the SRS digest and for
/// 'manifest.sha256', so the manifest hashes the same bytes 'sha256sum -c' is
/// later pointed at.
fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

/// The 256-byte EIP-2537 padded form of a G2 point, as hex: eight 32-byte words
/// x.c0_hi, x.c0_lo, x.c1_hi, x.c1_lo, y.c0_hi, y.c0_lo, y.c1_hi, y.c1_lo.
///
/// This is NOT a second encoder. It calls '__test_only_g2_to_u256s', which is the
/// crate's own 'lowering::encoding::g2_to_u256s' - the exact function the
/// generated verifier's constructor embeds. Exporting through it means the pin
/// the Lean side checks is the pin the Solidity side actually uses.
fn g2_eip_hex(p: &midnight_curves::G2Projective) -> String {
    let words = __test_only_g2_to_u256s(&p.to_affine());
    let mut out = Vec::with_capacity(256);
    for w in words {
        out.extend_from_slice(&w.to_be_bytes::<32>());
    }
    debug_assert_eq!(out.len(), 256);
    hex::encode(out)
}

/// The SRS as one canonical byte string: ParamsKZG::write_custom in
/// SerdeFormat::Processed - k, every monomial G1 power, every Lagrange G1 power,
/// then g2 and s_g2. Hashing this pins the whole SRS rather than only its two G2
/// elements, so a different trapdoor cannot slip through while g2 and s_g2
/// happen to agree.
fn srs_bytes(srs: &Params) -> Vec<u8> {
    let mut buf = Vec::new();
    srs.write_custom(&mut buf, SerdeFormat::Processed)
        .expect("serialize the SRS for its manifest digest");
    buf
}

/// Build the SRS this mode asks for, and - for the seeded mode - the trapdoor it
/// was built with.
///
/// 'unsafe_setup' draws the toxic scalar as the FIRST thing it takes from the rng
/// (params.rs:106, 'let s = <E::Fr>::random(rng)'), before any parallel work. So
/// a second stream from the same seed reproduces exactly that scalar, and the
/// assert below proves the re-derivation is the real one rather than a guess that
/// happens to look plausible. Bls12::Fr IS Fq (curves/src/bls12_381/mod.rs:31),
/// the same 'F' this circuit is built over, so the scalar needs no conversion.
fn build_srs(mode: &SrsMode, relation: &PoseidonExample) -> (Params, Option<F>) {
    match mode {
        SrsMode::Filecoin => {
            let srs_dir = env::var("SRS_DIR").unwrap_or_else(|_| {
                concat!(env!("CARGO_MANIFEST_DIR"), "/../../zk_stdlib/examples/assets").to_string()
            });
            env::set_var("SRS_DIR", &srs_dir);
            (srs_for_test(relation, Some(K)), None)
        }
        SrsMode::Unsafe { seed } => {
            let s = F::random(ChaCha8Rng::seed_from_u64(*seed));
            let srs = Params::unsafe_setup(K, ChaCha8Rng::seed_from_u64(*seed));
            assert_eq!(
                srs.g2() * s,
                srs.s_g2(),
                "REF.11 stop condition: the trapdoor re-derived from seed {seed} does not \
                 generate the SRS's own s_g2, so it is not that SRS's trapdoor"
            );
            assert_eq!(
                midnight_curves::G2Projective::generator() * s,
                srs.s_g2(),
                "REF.11: the SRS's g2 must be the standard generator, or the exported \
                 g2_eip_hex pins a different deployment than the pairing check uses"
            );
            (srs, Some(s))
        }
    }
}

/// Run the real verifier pipeline on one candidate proof and return
/// '(verdict, error_class)' exactly as the honest run above does it: 'prepare'
/// for the transcript framing and the algebraic identities, then the pairing
/// check 'prepare' deliberately leaves to the caller (poly/kzg/msm.rs:284).
///
/// The mutation corpus is scored with this and nothing else, so a mutant's
/// recorded verdict is the verifier's own answer, not the exporter's opinion.
fn run_verifier(
    vk: &Vk,
    params_verifier: &midnight_proofs::poly::kzg::params::ParamsVerifierKZG<Bls12>,
    committed_pi: &[G1Projective],
    pi: &[F],
    candidate: &[u8],
) -> (String, serde_json::Value) {
    let mut transcript = Recording::init_from_bytes(candidate);
    let committed: [&[G1Projective]; 1] = [committed_pi];
    let public: [&[F]; 1] = [pi];
    match prepare::<F, KZGCommitmentScheme<Bls12>, Recording>(
        vk,
        &committed,
        &[&public],
        &mut transcript,
    ) {
        Ok(guard) => match transcript.assert_empty() {
            Ok(()) => {
                if guard.check(params_verifier) {
                    ("accept".to_string(), serde_json::Value::Null)
                } else {
                    ("reject".to_string(), json!("opening"))
                }
            }
            Err(_) => ("reject".to_string(), json!("transcript_notFound")),
        },
        Err(Error::InvalidInstances) => ("reject".to_string(), json!("invalidInstances")),
        Err(Error::Opening) => ("reject".to_string(), json!("opening")),
        Err(Error::Transcript(e)) => (
            "reject".to_string(),
            json!(format!("transcript:{:?}", e.kind())),
        ),
        Err(other) => ("reject".to_string(), json!(format!("{other:?}"))),
    }
}

fn out_dir(mode: &SrsMode) -> PathBuf {
    if let Ok(dir) = env::var("MIDFALL_CONFORMANCE_OUT") {
        return PathBuf::from(dir);
    }
    mode.default_dir()
}

// ---------------------------------------------------------------------------
// REF.11: the EVM leg
// ---------------------------------------------------------------------------

/// Render, deploy and call the generated Solidity verifier on the SAME proof the
/// native verifier just accepted, and record what it said. This is the leg that
/// makes the bundle a *reference gate* rather than a Rust-only trace: acceptance
/// is checked against the artifact Lean's calldata has to match.
///
/// Requires the 'evm' feature (revm + the pinned solc). Without it the file is
/// still written, with 'evm_executed: false', so the bundle's shape does not
/// depend on the feature set and a reader can tell the two apart.
#[cfg(feature = "evm")]
fn evm_leg(
    generator: &SolidityGenerator<'_>,
    calldata: &[u8],
    native_verdict: &str,
) -> serde_json::Value {
    use halo2_solidity_verifier::{
        compile_solidity, solc_version, CallOutcome, Evm, QuotientLowering, RenderOptions, RenderVk,
    };
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            quotient_lowering: QuotientLowering::Vm,
            ..RenderOptions::default()
        })
        .expect("render the verifier for the EVM leg");
    let verifier_solidity = artifacts.verifier;
    let vk_solidity = artifacts
        .verifying_key
        .expect("a separate-VK render includes the VK");

    let mut evm = Evm::default();
    let vk_address = evm.create(compile_solidity(&vk_solidity));
    let verifier_address =
        evm.create_with_address_arg(compile_solidity(&verifier_solidity), vk_address);

    let (status, accepted, gas_used, output_hex) =
        match evm.try_call_with_gas(verifier_address, calldata.to_vec(), 5_000_000_000) {
            CallOutcome::Success { gas_used, output, .. } => (
                "success".to_string(),
                output == [vec![0u8; 31], vec![1]].concat(),
                gas_used,
                hex::encode(&output),
            ),
            CallOutcome::Revert { gas_used, output } => {
                ("revert".to_string(), false, gas_used, hex::encode(&output))
            }
            CallOutcome::Halt { gas_used, reason } => {
                ("halt".to_string(), false, gas_used, format!("{reason}"))
            }
        };

    assert!(
        accepted,
        "REF.11: the generated Solidity verifier must ACCEPT the proof the native verifier \
         accepted (native verdict = {native_verdict}); status={status} output=0x{output_hex}"
    );

    json!({
        "schema": 1,
        "evm_executed": true,
        "engine": "revm 19 (Prague, EIP-2537 precompiles)",
        "solc": solc_version().unwrap_or_else(|e| format!("unavailable: {e}")),
        "quotient_lowering": "Vm",
        "render_vk": "Separate",
        "calldata_len": calldata.len(),
        "calldata_sha256": sha256_hex(calldata),
        "status": status,
        "accepted": accepted,
        "gas_used": gas_used,
        "output_hex": output_hex,
        "native_verdict": native_verdict,
        "note": "the same proof.bin, instances and SRS as the native run; calldata.bin is the \
                 exact bytes of this call.",
    })
}

/// The 'evm' feature is off, so nothing was deployed. Recorded rather than faked:
/// the calldata is still the real encoder's output, but no EVM verdict exists.
#[cfg(not(feature = "evm"))]
fn evm_leg(
    _generator: &SolidityGenerator<'_>,
    calldata: &[u8],
    native_verdict: &str,
) -> serde_json::Value {
    json!({
        "schema": 1,
        "evm_executed": false,
        "reason": "this test binary was built without the 'evm' feature; re-run with \
                   --features rust-verifier-trace,evm and SOLC pointed at the pinned solc to \
                   produce the EVM leg",
        "calldata_len": calldata.len(),
        "calldata_sha256": sha256_hex(calldata),
        "native_verdict": native_verdict,
    })
}

// ---------------------------------------------------------------------------
// The export
// ---------------------------------------------------------------------------

#[test]
fn export_poseidon_conformance_bundle() {
    // REF.11: which SRS this bundle is built under. F0 (filecoin) and F1
    // (unsafe-seeded) own separate bundle directories, so neither export can
    // overwrite the other. See SrsMode.
    let srs_mode = SrsMode::from_env();
    let relation = PoseidonExample;
    let (srs, trapdoor): (Params, Option<F>) = build_srs(&srs_mode, &relation);
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    let vk: &Vk = vk.vk();

    let mut rng = ChaCha8Rng::seed_from_u64(42);
    let witness: [F; 3] = core::array::from_fn(|_| F::random(&mut rng));
    let instance = <PoseidonChip<F> as HashCPU<F, F>>::hash(&witness);
    let prover_rng = ChaCha8Rng::seed_from_u64(0xdebd);
    let proof = midnight_zk_stdlib::prove::<PoseidonExample, Keccak256>(
        &srs,
        &pk,
        &relation,
        &instance,
        witness,
        prover_rng,
    )
    .expect("poseidon proof generation must succeed");
    let pi = PoseidonExample::format_instance(&instance).expect("format_instance");

    // Fixture selection. The committed fixtures/poseidon/{proof.bin,instance.be}
    // can be exported instead of a freshly generated proof, by setting
    // MIDFALL_CONFORMANCE_FIXTURE=committed. That is the bundle whose trace should
    // equal the committed rust_trace.json, which is what makes the third leg of the
    // comparison (exporter vs committed reference) possible.
    let mode = env::var("MIDFALL_CONFORMANCE_FIXTURE")
        .unwrap_or_else(|_| "regenerated".into());

    // Compare with the committed fixture. Reported, never assumed.
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/poseidon");
    let read_fixture = |name: &str| fs::read(fixture_dir.join(name)).ok();
    let committed_proof = read_fixture("proof.bin");
    let committed_instance = read_fixture("instance.be");
    let fixture_match = json!({
        "proof": committed_proof.as_deref() == Some(proof.as_slice()),
        "instance": committed_instance.as_deref()
            == Some(<F as PrimeField>::to_repr(&instance).as_ref()),
        "committed_proof_len": committed_proof.as_ref().map(Vec::len),
        "exported_proof_len": proof.len(),
    });

    let (proof, pi) = if mode == "committed" {
        let raw = fs::read(fixture_dir.join("proof.bin")).expect("committed proof.bin");
        let mut repr = <F as PrimeField>::Repr::default();
        repr.as_mut().copy_from_slice(fs::read(fixture_dir.join("instance.be")).expect("committed instance.be").as_slice());
        // NOTE: the committed instance.be is BIG-endian (the transcript absorb
        // form), not the little-endian PrimeField::Repr that
        // tests/poseidon_fixture.rs writes with to_repr. Try the wire order
        // first and fall back to the reversed one, and record which worked.
        let le = Option::<F>::from(F::from_repr(repr));
        let mut rev = repr;
        rev.as_mut().reverse();
        let be = Option::<F>::from(F::from_repr(rev));
        let inst = le.or(be).expect("committed instance.be is a canonical repr in neither byte order");
        eprintln!("[conformance-export] committed instance.be decoded as {}", if le.is_some() { "little-endian repr" } else { "big-endian absorb" });
        (raw, PoseidonExample::format_instance(&inst).expect("format_instance"))
    } else {
        (proof, pi)
    };

    // --- the run: real verifier, recording transcript, trace hooks on ---------
    let committed_pi = [G1Projective::identity()];
    solidity_trace::start();
    let mut transcript = Recording::init_from_bytes(&proof);
    let prepare_out = prepare::<F, KZGCommitmentScheme<Bls12>, Recording>(
        vk,
        &[&committed_pi],
        &[&[pi.as_slice()]],
        &mut transcript,
    );
    let trace_events = solidity_trace::take();
    let (guard, verdict, error_class) = match prepare_out {
        Ok(guard) => match transcript.assert_empty() {
            Ok(()) => (Some(guard), "prepare_ok", serde_json::Value::Null),
            Err(_) => (None, "reject", json!("transcript_notFound")),
        },
        Err(Error::InvalidInstances) => (None, "reject", json!("invalidInstances")),
        Err(Error::Opening) => (None, "reject", json!("opening")),
        Err(Error::Transcript(e)) => (None, "reject", json!(format!("transcript:{:?}", e.kind()))),
        Err(other) => (None, "reject", json!(format!("{other:?}"))),
    };

    // The pairing check, which `prepare` deliberately does not run.
    let params_verifier = srs.verifier_params();
    let pairing_check = match guard.clone() {
        Some(g) => g.check(&params_verifier),
        None => false,
    };
    let verdict = if pairing_check { "accept" } else { verdict };
    if !pairing_check {
        eprintln!(
            "[conformance-export] mode={} REJECTED verdict={} error={:?} proof={} bytes",
            mode, verdict, error_class, proof.len()
        );
    }
    if !pairing_check && mode == "committed" {
        // FINDING, reported rather than worked around: the committed
        // fixtures/poseidon/proof.bin does not verify under the feature profile the
        // trace hooks require (`rust-verifier-trace`, which forces
        // `truncated-challenges`). `prepare` returns Error::Opening, i.e. the
        // algebraic identities fail, so the committed proof was produced by a
        // different prover profile than any reachable here. Under
        // `rust-verifier-trace,fewer-point-sets` the regenerated proof grows to 4848
        // bytes / 141 reads against the committed 4752 / 138, and the instance from
        // seed 42 never equals instance.be, so the committed fixture is not
        // reproducible from this tree at all. That is a baseline/provenance question,
        // not a harness question (brief hazard 1), so this mode reports and exits.
        eprintln!(
            "[conformance-export] FINDING: the committed fixture was REJECTED by the native verifier \n             under this feature profile (verdict={verdict}, error={error_class:?}); no bundle written. \n             The regenerated bundle is the one the Lean runner replays."
        );
        return;
    }
    assert!(
        pairing_check,
        "poseidon conformance export: the native verifier must accept the honest proof (mode {mode})"
    );

    // --- align squeezes with the recorded challenge names ---------------------
    let challenge_events: Vec<_> =
        trace_events.iter().filter(|e| is_challenge_id(e.id)).cloned().collect();
    let squeeze_count = transcript.squeeze_count();
    assert_eq!(
        challenge_events.len(),
        squeeze_count,
        "exporter: {} squeezes were performed but {} challenge values were traced; the alignment between the transcript log and the trace hooks is not derivable",
        squeeze_count,
        challenge_events.len()
    );

    // Reads get their names from the proof_* trace events, in push order.
    let read_names: Vec<String> =
        trace_events.iter().filter(|e| is_proof_read_id(e.id)).map(|e| e.name.to_string()).collect();
    let log_reads = transcript.events.iter().filter(|e| matches!(e, Ev::Read { .. })).count();
    let mut widths: std::collections::BTreeMap<usize, usize> = Default::default();
    for e in transcript.events.iter() {
        if let Ev::Read { wire, .. } = e {
            *widths.entry(wire.len()).or_insert(0) += 1;
        }
    }
    eprintln!(
        "[conformance-export] proof={} bytes, transcript reads={} widths={:?}, traced proof reads={}, cursor={}",
        proof.len(),
        log_reads,
        widths,
        read_names.len(),
        transcript.inner.buffer().position()
    );
    assert_eq!(
        read_names.len(),
        log_reads,
        "exporter: {} transcript reads but {} traced proof reads",
        log_reads,
        read_names.len()
    );

    // --- the absorb prefix, named from the VK data rather than guessed --------
    // parse_trace absorbs: transcript_repr, then every committed instance
    // commitment, then per instance column the column length and its values
    // (proofs/src/plonk/verifier.rs:71-105).
    let mut expected_prefix: Vec<String> = vec!["vk_repr".to_string()];
    for i in 0..NUM_COMMITTED_INSTANCES {
        expected_prefix.push(format!("committed_instance[{i}]"));
    }
    for (c, column) in [pi.as_slice()].into_iter().enumerate() {
        expected_prefix.push(format!("instance_len[{c}]"));
        for v in 0..column.len() {
            expected_prefix.push(format!("instance[{c}][{v}]"));
        }
    }
    let absorbed: Vec<&Vec<u8>> = transcript
        .events
        .iter()
        .filter_map(|e| match e {
            Ev::Absorb { bytes, .. } => Some(bytes),
            _ => None,
        })
        .collect();
    assert_eq!(
        absorbed.len(),
        expected_prefix.len(),
        "exporter: the verifier absorbed {} prefix items but the VK shape predicts {};          the instance/committed-instance shape is exactly what docs/ecosystem.md section 11          says was unknown, so a mismatch here must be an exporter error, not a silent gap",
        absorbed.len(),
        expected_prefix.len()
    );

    // --- build the log --------------------------------------------------------
    let mut prefix_i = 0;
    let mut read_i = 0;
    let mut squeeze_i = 0;
    let mut since_squeeze: Vec<String> = Vec::new();
    let mut log = Vec::new();
    for event in &transcript.events {
        match event {
            Ev::Absorb { bytes, .. } => {
                let tag = expected_prefix[prefix_i].clone();
                prefix_i += 1;
                since_squeeze.push(hex::encode(bytes));
                log.push(json!({
                    "kind": "absorb", "tag": tag, "bytes_be_hex": hex::encode(bytes)
                }));
            }
            Ev::Read { wire, absorbed, .. } => {
                let name = read_names[read_i].clone();
                read_i += 1;
                since_squeeze.push(hex::encode(absorbed));
                log.push(json!({
                    "kind": "read",
                    "tag": name,
                    "index": read_i - 1,
                    "wire_hex": hex::encode(wire),
                    "absorbed_be_hex": hex::encode(absorbed),
                }));
            }
            Ev::Squeeze { digest, .. } => {
                let ch = &challenge_events[squeeze_i];
                squeeze_i += 1;
                log.push(json!({
                    "kind": "squeeze",
                    "name": ch.name,
                    "digest_be_hex": hex::encode(digest),
                    "challenge_be_hex": hex::encode(&ch.data),
                    "absorbed_before_hex": since_squeeze,
                }));
                since_squeeze.clear();
            }
        }
    }

    // --- DualMSM terms --------------------------------------------------------
    let (left_terms, right_terms) = match &guard {
        Some(g) => g.split(),
        None => (Vec::new(), Vec::new()),
    };
    let encode_terms = |terms: &Vec<(&CommitmentLabel, &F, &G1Projective)>| -> Vec<_> {
        terms
            .iter()
            .map(|(label, scalar, point)| {
                json!({
                    "label": label.to_string(),
                    "scalar_be_hex": be_hex(scalar),
                    "point_compressed_hex": point_hex(point),
                })
            })
            .collect()
    };
    let channel_eval = |terms: &Vec<(&CommitmentLabel, &F, &G1Projective)>| -> String {
        // Mirrors DualMSM::check (poly/kzg/msm.rs:283-292), including its
        // single-term shortcut, so the exported point is the one the pairing sees.
        if terms.len() == 1 && *terms[0].1 == F::ONE {
            point_hex(terms[0].2)
        } else {
            let scalars: Vec<F> = terms.iter().map(|(_, s, _)| **s).collect();
            let bases: Vec<G1Projective> = terms.iter().map(|(_, _, p)| **p).collect();
            point_hex(&msm_specific::<G1Affine>(&scalars, &bases))
        }
    };

    let cs = vk.cs();
    let domain = vk.get_domain();
    let selector_flags: Vec<_> = (0..cs.num_fixed_columns())
        .map(|i| json!({"is_simple": cs.has_simple_selector_col(i), "col_idx": i}))
        .collect();
    let instance_queries: Vec<_> =
        cs.instance_queries().iter().map(|(col, rot)| json!([col.index(), rot.0])).collect();
    let advice_queries: Vec<_> =
        cs.advice_queries().iter().map(|(col, rot)| json!([col.index(), rot.0])).collect();
    let fixed_queries: Vec<_> =
        cs.fixed_queries().iter().map(|(col, rot)| json!([col.index(), rot.0])).collect();

    let vk_json = json!({
        "schema": 1,
        "k": domain.k(),
        "n": vk.n(),
        "omega_be_hex": be_hex(&domain.get_omega()),
        "omega_inv_be_hex": be_hex(&domain.get_omega_inv()),
        "cs_degree": cs.degree(),
        "quotient_poly_degree": domain.get_quotient_poly_degree(),
        "transcript_repr_be_hex": be_hex(&vk.transcript_repr()),
        "num_advice_columns": cs.num_advice_columns(),
        "num_fixed_columns": cs.num_fixed_columns(),
        "num_instance_columns": cs.num_instance_columns(),
        "num_challenges": cs.num_challenges(),
        "nb_public_inputs": pi.len(),
        "num_committed_instances": NUM_COMMITTED_INSTANCES,
        "fixed_commitments_compressed_hex": vk.fixed_commitments().iter().map(point_hex).collect::<Vec<_>>(),
        "permutation_commitments_compressed_hex": vk.permutation().commitments().iter().map(point_hex).collect::<Vec<_>>(),
        "advice_column_phase": cs.advice_column_phase(),
        "selector_flags": selector_flags,
        "instance_queries": instance_queries,
        "advice_queries": advice_queries,
        "fixed_queries": fixed_queries,
        "blinding_factors": cs.blinding_factors(),
        "num_lookups": cs.lookups().len(),
        "num_trashcans": cs.trashcans().len(),
        "truncated_challenges": true,
        "scalar_num_bits": <F as PrimeField>::NUM_BITS,
        "extended_k": domain.extended_k(),
    });

    // REF.11 schema 2: the SRS provenance the acceptance gate needs. The
    // 'schema' integer is deliberately left at 1 - the card's acceptance is that
    // the Filecoin bundle's EXISTING fields stay byte-identical apart from added
    // keys, and the committed Lean importer parses schema 1. 'schema_extension'
    // names the additive version instead, so a reader can tell which keys are new
    // without a breaking change.
    //
    // The three *_eip_hex fields are the 256-byte EIP-2537 padded forms the
    // generated verifier's constructor embeds, produced by the verifier's own
    // encoder (see g2_eip_hex). 'neg_s_g2_eip_hex' is -s*G2, the second pairing
    // argument; 'n_g2_compressed_hex' above stays -G2, the first one.
    //
    // 'srs_sha256' hashes the whole serialized SRS, not just the two G2 points:
    // pinning g2 and s_g2 alone would not pin the 2^k G1 powers the commitments
    // are made from.
    let mut params_json = json!({
        "schema": 1,
        "schema_extension": 2,
        "curve": "BLS12-381",
        "format": "compressed",
        "g1_compressed_hex": point_hex(&G1Projective::generator()),
        "g2_compressed_hex": g2_hex(&srs.g2().into()),
        "s_g2_compressed_hex": g2_hex(&srs.s_g2().into()),
        "n_g2_compressed_hex": g2_hex(&(-srs.g2()).into()),
        "note": "n_g2 is -g2, the negated generator the final pairing uses                  (poly/kzg/msm.rs:283-292 builds the second term from n_g2_prepared).",
        "max_k": midnight_proofs::poly::commitment::Params::max_k(&srs),
        "srs_kind": srs_mode.kind(),
        "srs_seed": srs_mode.seed(),
        "srs_seed_hex": srs_mode.seed().map(|s| format!("{s:#018x}")),
        "trapdoor_s_be_hex": trapdoor.map(|s| be_hex(&s)),
        "g2_eip_hex": g2_eip_hex(&srs.g2()),
        "s_g2_eip_hex": g2_eip_hex(&srs.s_g2()),
        "neg_s_g2_eip_hex": g2_eip_hex(&(-srs.s_g2())),
        "srs_sha256": sha256_hex(&srs_bytes(&srs)),
    });
    if trapdoor.is_none() {
        // F0's trapdoor is the ceremony's secret: absent, not zero and not guessed.
        params_json["trapdoor_note"] = json!("unknown: the Filecoin ceremony SRS has no exported trapdoor (D-P63 is about F1 only)");
    } else {
        params_json["trapdoor_note"] = json!("PUBLIC by construction (D-P63): no soundness of the proof system is claimed for this SRS");
    }

    let instances_json = json!({
        "schema": 1,
        "committed": [[point_hex(&committed_pi[0])]],
        "public": [[be_hex(&pi[0])]],
        "note": "committed instances go first; the public column is                  Relation::format_instance(instance), one value for poseidon.",
    });

    let trace_json = json!({
        "schema": 1,
        "fixture": "poseidon",
        "verdict": verdict,
        "error": error_class,
        "pairing_check": pairing_check,
        "proof_len": proof.len(),
        // REF.11: the proof as hex alongside proof.bin, so a reader that only
        // parses JSON (the Lean runner) can pin the exact bytes without a second
        // file, and so trace.json alone carries the run it describes.
        "proof_hex": hex::encode(&proof),
        "srs_kind": srs_mode.kind(),
        "srs_seed": srs_mode.seed(),
        // Stated in the bundle, not only in the docs, because it changes what a
        // reader may conclude from manifest.sha256. The prover's inter-limb
        // quotient blinding draws from OsRng (proofs/src/plonk/prover.rs:121-131,
        // blind_quotient_limbs under cfg(not(single-h-commitment))), so proof.bin
        // differs on every export run - and with it trace.json, calldata.bin,
        // evm.json and mutations.json. What DOES reproduce byte for byte is the
        // circuit-and-SRS half: vk.json, cs.json, params.json, instances.json.
        // Fixing the prover is a proofs/src change and out of scope (D-P58), so the
        // honest contract is: one bundle is one run, pinned by its manifest.
        "reproducibility": {
            "deterministic_files": ["vk.json", "cs.json", "params.json", "instances.json"],
            "run_dependent_files": ["proof.bin", "trace.json", "calldata.bin", "evm.json", "mutations.json"],
            "run_dependent_because": "blind_quotient_limbs calls F::random(OsRng) (proofs/src/plonk/prover.rs:121-131); the seeded prover_rng does not reach it",
            "pinned_by": "manifest.sha256",
        },
        "fixture_match": fixture_match,
        "transcript_log": log,
        "dual_msm": {
            "left": encode_terms(&left_terms),
            "right": encode_terms(&right_terms),
            "left_eval_compressed_hex": channel_eval(&left_terms),
            "right_eval_compressed_hex": channel_eval(&right_terms),
        },
        "solidity_trace": trace_events.iter().map(|e| json!({
            "id": e.id, "name": e.name, "data_hex": hex::encode(&e.data),
        })).collect::<Vec<_>>(),
    });

    // --- F.1: the constraint system ITSELF, as data ---------------------------
    //
    // The four structures vk.json never carried - gates, lookups, trashcans and
    // permutation.columns - are what `ProtocolPlan::from_constraint_system` reads and
    // therefore what C.4's protocol-caused refutations have been waiting for. They are
    // written to a SIBLING file rather than into vk.json: vk.json's schema is already
    // parsed by `Instances/PoseidonEnv.lean` field by field, and a gate is a nested
    // tree, not a scalar. Nothing here is computed by the exporter beyond what the
    // reference's own accessors return; the values are the deployment's, read out of
    // the same `vk.cs()` the native verifier just checked the proof against.
    let cs_degree = cs.degree();
    let perm_cols = cs.permutation().get_columns();
    let permutation_columns: Vec<_> = perm_cols
        .iter()
        .map(|c| match c.column_type() {
            Any::Advice(a) => json!({"type": "advice", "index": c.index(), "phase": a.phase()}),
            Any::Fixed => json!({"type": "fixed", "index": c.index(), "phase": null}),
            Any::Instance => json!({"type": "instance", "index": c.index(), "phase": null}),
        })
        .collect();
    let gates: Vec<_> = cs
        .gates()
        .iter()
        .map(|g| {
            json!({
                "name": g.name(),
                "constraint_names": (0..g.polynomials().len())
                    .map(|i| g.constraint_name(i).to_string())
                    .collect::<Vec<_>>(),
                "polys": g.polynomials().iter().map(expr_json).collect::<Vec<_>>(),
                "queried_selectors": g.queried_selectors().iter()
                    .map(|s| json!({"index": s.index(), "is_simple": s.is_simple()}))
                    .collect::<Vec<_>>(),
            })
        })
        .collect();
    // `chunk_by_degree(cs_degree)` is the exact call PM:344 makes, so the exported
    // num_chunks is the reference's own answer and the Lean importer can KAT its port
    // of `LogupBatchedArgument::num_chunks` against it. `input_expressions` is the
    // flattened chunk list: `chunk_by_degree` partitions `input_expressions` in order
    // (logup.rs:326-338), so flattening restores it exactly.
    let lookups: Vec<_> = cs
        .lookups()
        .iter()
        .map(|l| {
            let chunked = l.chunk_by_degree(cs_degree);
            let chunks = chunked.input_expression_chunks();
            json!({
                "selector": expr_json(l.selector_expression()),
                "table_expressions": l.table_expressions().iter().map(expr_json).collect::<Vec<_>>(),
                "input_expressions": chunks.iter().flatten()
                    .map(|pl| pl.iter().map(expr_json).collect::<Vec<_>>())
                    .collect::<Vec<_>>(),
                "num_parallel_lookups": chunks.iter().flatten().count(),
                "num_chunks_at_cs_degree": chunked.num_chunks(),
            })
        })
        .collect();
    let trashcans: Vec<_> = cs
        .trashcans()
        .iter()
        .map(|t| {
            json!({
                "name": t.name(),
                "selector": expr_json(t.selector()),
                "constraint_expressions": t.constraint_expressions().iter().map(expr_json).collect::<Vec<_>>(),
            })
        })
        .collect();
    let cs_json = json!({
        "schema": 1,
        "source": "proofs/solidity-verifier/tests/conformance_export.rs (F.1 half 1)",
        "cs_degree": cs_degree,
        "blinding_factors": cs.blinding_factors(),
        "num_simple_selectors": cs.num_simple_selectors(),
        "challenge_phase": cs.challenge_phase(),
        "permutation_columns": permutation_columns,
        "gates": gates,
        "lookups": lookups,
        "trashcans": trashcans,
        // Cross-checks: the reference's own summary numbers, restated next to the
        // structures they summarize so an importer that drops a subtree cannot pass a
        // count gate by accident.
        "summary": {
            "num_gates": gates.len(),
            "gate_poly_total": cs.gates().iter().map(|g| g.polynomials().len()).sum::<usize>(),
            "num_lookups": cs.lookups().len(),
            "num_trashcans": cs.trashcans().len(),
            "num_permutation_columns": perm_cols.len(),
        },
        // Recorded, not hidden: five ConstraintSystem fields have NO public accessor
        // outside proofs/src, so they are absent from this file and the importer must
        // take them from ConstraintSystem.default. None is read by the plan path;
        // `cs_degree` above is what proves `minimum_degree` did not bind here.
        "not_exported": [
            "gate.queried_cells (circuit.rs:1627, pub(crate))",
            "lookup name (logup.rs:172, pub(crate), no accessor)",
            "minimum_degree (circuit.rs:1726, pub(crate), no accessor)",
            "unblinded_advice_columns (circuit.rs:1687, pub(crate), no accessor)",
            "general_column_annotations (circuit.rs:1720, pub(crate), no accessor)"
        ],
    });

    // --- REF.11: where each proof read lives in proof.bin ---------------------
    //
    // The transcript reads the proof strictly left to right, so the byte range of
    // read i is the running sum of the widths recorded on the earlier reads. The
    // exporter does not guess the layout: it takes the widths from the same
    // Recording the accepted run went through, and asserts they tile the proof.
    let mut reads: Vec<(String, usize, usize)> = Vec::new();
    {
        let mut cursor = 0usize;
        let mut it = read_names.iter();
        for e in &transcript.events {
            if let Ev::Read { wire, .. } = e {
                let name = it.next().cloned().unwrap_or_else(|| "?untitled".to_string());
                reads.push((name, cursor, wire.len()));
                cursor += wire.len();
                assert_eq!(
                    &proof[cursor - wire.len()..cursor],
                    wire.as_slice(),
                    "exporter: read {} is not the bytes the transcript actually consumed",
                    reads.len() - 1
                );
            }
        }
        assert_eq!(
            cursor,
            proof.len(),
            "exporter: the {} transcript reads cover {} bytes but proof.bin is {} bytes, so a \
             mutation corpus keyed on read offsets would miss part of the proof",
            reads.len(),
            cursor,
            proof.len()
        );
    }

    // --- REF.11: the mutation corpus -------------------------------------------
    //
    // One single-bit mutation per read - the low bit of that read's first byte -
    // plus the structural set the card names (a truncation and an appended byte).
    // Every mutant goes back through the REAL verifier (run_verifier), so the
    // recorded verdict and error class are the verifier's own answer and REF.12
    // can replay the corpus against Lean and compare classes rather than re-derive
    // them. Nothing here is assumed to reject: an accepting mutant is a finding, so
    // it is counted and printed rather than hidden.
    let mut mutants: Vec<serde_json::Value> = Vec::new();
    {
        let record =
            |tag: &str,
             kind: &str,
             read_index: Option<usize>,
             byte_offset: Option<usize>,
             bit: Option<u8>,
             candidate: Vec<u8>,
             out: &mut Vec<serde_json::Value>| {
            let (verdict, error) =
                run_verifier(vk, &params_verifier, &committed_pi, &pi, &candidate);
            out.push(json!({
                "tag": tag,
                "kind": kind,
                "read_index": read_index,
                "read_name": read_index.map(|i| reads[i].0.clone()),
                "byte_offset": byte_offset,
                "bit": bit,
                "len": candidate.len(),
                "sha256": sha256_hex(&candidate),
                "verdict": verdict,
                "error": error,
            }));
        };

        for (i, (_, off, _)) in reads.iter().enumerate() {
            let mut m = proof.clone();
            m[*off] ^= 0x01;
            record(
                &format!("read[{}].first_byte.bit0", i),
                "single_bit_flip",
                Some(i),
                Some(*off),
                Some(0),
                m,
                &mut mutants,
            );
        }

        // The structural set: shapes a single bit flip cannot produce.
        let mut trunc1 = proof.clone();
        trunc1.pop();
        record("truncate_last_byte", "truncation", None, Some(proof.len() - 1), None, trunc1, &mut mutants);
        let mut trunc_half = proof.clone();
        trunc_half.truncate(proof.len() / 2);
        record("truncate_half", "truncation", None, Some(proof.len() / 2), None, trunc_half, &mut mutants);
        let mut appended = proof.clone();
        appended.push(0x00);
        record("append_zero_byte", "trailing_byte", None, Some(proof.len()), None, appended, &mut mutants);
        record("empty_proof", "truncation", None, Some(0), None, Vec::new(), &mut mutants);
        // The honest proof itself, scored through the same path, so a reader can
        // see the corpus harness agrees with trace.json's verdict before trusting
        // any of the rejects.
        record("unmutated", "control", None, None, None, proof.clone(), &mut mutants);

        let accepted: Vec<&str> = mutants
            .iter()
            .filter(|m| m["verdict"] == json!("accept"))
            .map(|m| m["tag"].as_str().unwrap_or("?"))
            .collect();
        if accepted.len() != 1 || accepted[0] != "unmutated" {
            eprintln!(
                "[conformance-export] FINDING: the mutation corpus did not behave as expected; \
                 accepted = {:?}",
                accepted
            );
        }
    }

    let mutations_json = json!({
        "schema": 1,
        "fixture": "poseidon",
        "srs_kind": srs_mode.kind(),
        "proof_len": proof.len(),
        "reads": reads.iter().enumerate().map(|(i, (name, off, len))| json!({
            "index": i, "name": name, "offset": off, "len": len,
        })).collect::<Vec<_>>(),
        "corpus_size": mutants.len(),
        "single_bit_per_read": reads.len(),
        "structural": 4,
        "control": 1,
        "mutants": mutants,
        "note": "each mutant is scored by the real Rust verifier (prepare + the KZG pairing \
                 check), so verdict and error are what REF.12 must reproduce in Lean.",
    });

    // --- REF.11: the EVM leg, from the same run --------------------------------
    let generator = SolidityGenerator::new(
        &srs,
        vk,
        GeneratorConfig::new(pi.len(), NUM_COMMITTED_INSTANCES),
    );
    let calldata = generator
        .encode_calldata(&proof, &pi)
        .expect("the generated verifier must encode this proof as calldata");
    let evm_json = evm_leg(&generator, &calldata, verdict);

    // --- write the bundle -------------------------------------------------------
    let dir = if mode == "committed" { PathBuf::from(out_dir(&srs_mode).to_str().unwrap().to_string() + "_committed") } else { out_dir(&srs_mode) };
    fs::create_dir_all(&dir).expect("create the conformance output directory");
    let write_json = |dir: &Path, name: &str, v: &serde_json::Value| {
        fs::write(dir.join(name), serde_json::to_string_pretty(v).unwrap())
            .unwrap_or_else(|e| panic!("write {name}: {e}"));
    };
    write_json(&dir, "vk.json", &vk_json);
    write_json(&dir, "params.json", &params_json);
    write_json(&dir, "instances.json", &instances_json);
    fs::write(dir.join("proof.bin"), &proof).unwrap();
    write_json(&dir, "trace.json", &trace_json);
    write_json(&dir, "cs.json", &cs_json);
    fs::write(dir.join("calldata.bin"), &calldata).unwrap();
    write_json(&dir, "evm.json", &evm_json);
    write_json(&dir, "mutations.json", &mutations_json);

    // --- manifest.sha256 --------------------------------------------------------
    //
    // One bundle is ONE run: proof.bin is not reproducible across runs (see the
    // reproducibility block in trace.json), so the bundle is pinned by this
    // manifest rather than by regeneration. The format is plain 'sha256sum -c'
    // input, files in a fixed order, paths relative to the bundle directory.
    const BUNDLE_FILES: [&str; 9] = [
        "vk.json",
        "cs.json",
        "params.json",
        "instances.json",
        "proof.bin",
        "trace.json",
        "calldata.bin",
        "evm.json",
        "mutations.json",
    ];
    let mut manifest = String::new();
    for name in BUNDLE_FILES {
        let bytes = fs::read(dir.join(name)).unwrap_or_else(|e| panic!("read back {name}: {e}"));
        manifest.push_str(&format!("{}  {}\n", sha256_hex(&bytes), name));
    }
    fs::write(dir.join("manifest.sha256"), &manifest).expect("write manifest.sha256");

    let manifest_digest = sha256_hex(manifest.as_bytes());

    let identities = (0u64..)
        .take_while(|j| {
            trace_events.iter().any(|e| e.id == solidity_trace::QUOTIENT_IDENTITY_TRACE_BASE + j)
        })
        .count();
    eprintln!(
        "[conformance-export] {} srs={} verdict={verdict} pairing={pairing_check} log={} reads={} \
         identities={} trace_events={} proof={} bytes calldata={} mutants={} \
         manifest_sha256={} fixture_match={fixture_match}",
        dir.display(),
        srs_mode.kind(),
        log.len(),
        read_i,
        identities,
        trace_events.len(),
        proof.len(),
        calldata.len(),
        mutants.len(),
        manifest_digest,
    );
}
