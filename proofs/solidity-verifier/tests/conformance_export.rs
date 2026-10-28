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
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
};
use midnight_curves::{Bls12, Fq, G1Affine, G1Projective};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{prepare, solidity_trace, Error, VerifyingKey},
    poly::{
        kzg::{msm::msm_specific, KZGCommitmentScheme},
        CommitmentLabel,
    },
    transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
};
use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use serde_json::json;
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

fn out_dir() -> PathBuf {
    if let Ok(dir) = env::var("MIDFALL_CONFORMANCE_OUT") {
        return PathBuf::from(dir);
    }
    // tests live in proofs/solidity-verifier/tests; the bundle goes to the Lean tree.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../formal/fixtures/conformance/poseidon")
}

// ---------------------------------------------------------------------------
// The export
// ---------------------------------------------------------------------------

#[test]
fn export_poseidon_conformance_bundle() {
    let srs_dir = env::var("SRS_DIR").unwrap_or_else(|_| {
        concat!(env!("CARGO_MANIFEST_DIR"), "/../../zk_stdlib/examples/assets").to_string()
    });
    env::set_var("SRS_DIR", &srs_dir);
    let relation = PoseidonExample;
    let srs: Params = srs_for_test(&relation, Some(K));
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

    let params_json = json!({
        "schema": 1,
        "curve": "BLS12-381",
        "format": "compressed",
        "g1_compressed_hex": point_hex(&G1Projective::generator()),
        "g2_compressed_hex": g2_hex(&srs.g2().into()),
        "s_g2_compressed_hex": g2_hex(&srs.s_g2().into()),
        "n_g2_compressed_hex": g2_hex(&(-srs.g2()).into()),
        "note": "n_g2 is -g2, the negated generator the final pairing uses                  (poly/kzg/msm.rs:283-292 builds the second term from n_g2_prepared).",
        "max_k": midnight_proofs::poly::commitment::Params::max_k(&srs),
    });

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

    let dir = if mode == "committed" { PathBuf::from(out_dir().to_str().unwrap().to_string() + "_committed") } else { out_dir() };
    fs::create_dir_all(&dir).expect("create the conformance output directory");
    fs::write(dir.join("vk.json"), serde_json::to_string_pretty(&vk_json).unwrap()).unwrap();
    fs::write(dir.join("params.json"), serde_json::to_string_pretty(&params_json).unwrap())
        .unwrap();
    fs::write(dir.join("instances.json"), serde_json::to_string_pretty(&instances_json).unwrap())
        .unwrap();
    fs::write(dir.join("proof.bin"), &proof).unwrap();
    fs::write(dir.join("trace.json"), serde_json::to_string_pretty(&trace_json).unwrap()).unwrap();

    let identities = (0u64..)
        .take_while(|j| {
            trace_events.iter().any(|e| e.id == solidity_trace::QUOTIENT_IDENTITY_TRACE_BASE + j)
        })
        .count();
    eprintln!(
        "[conformance-export] {} verdict={verdict} pairing={pairing_check} log={} reads={} \
         identities={} trace_events={} proof={} bytes fixture_match={fixture_match}",
        dir.display(),
        log.len(),
        read_i,
        identities,
        trace_events.len(),
        proof.len(),
    );
}
