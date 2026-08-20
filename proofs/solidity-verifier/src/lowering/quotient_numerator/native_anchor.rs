// SPDX-License-Identifier: CC0-1.0
//! Native per-identity anchor (roadmap P5.a).
//!
//! Every generator-side quotient identity expression is evaluated over
//! memory reconstructed from a REAL midnight-proofs verifier run and
//! compared against the native verifier's own per-identity values
//! (`solidity_trace` ids `30_000 + global_index`), its y-batched numerator
//! (id 36), and its selector folds (`60_000 + bucket`).
//!
//! This is the tier-1 formula oracle for the permutation/lookup/trash
//! identities: unlike the frame differential (whose non-gate expressions are
//! re-parsed from the emitter's own Yul), the values compared here come from
//! `midnight_proofs::plonk::verifier` itself, so a transcription error in any
//! identity formula — gate, permutation, LogUp, or trash — mismatches. It
//! must stay green through the P5.b typed-builder swap.
//!
//! Needs `rust-verifier-trace` but deliberately NOT `evm`: no solc, no revm,
//! only native keygen/prove/prepare at k <= 6 (~100 ms per case).

use std::collections::BTreeMap;

use ff::{Field, PrimeField};
use group::Group;
use midnight_curves::{Bls12, Fq, G1Projective};
use midnight_proofs::{
    plonk::{
        create_proof, keygen_pk, keygen_vk_with_k, prepare,
        solidity_trace::{self, SolidityTraceEvent},
        Circuit,
    },
    poly::{
        commitment::Guard as _,
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
    },
    transcript::{CircuitTranscript, Transcript},
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::{
    api::GeneratorConfig,
    lowering::{
        layout::{trace, WORD_BYTES},
        plan::LoweringPlan,
        quotient_numerator::vm::{
            oracle::{
                eval_quotient_expr_with, expected_linearization_artifacts, QuotientOracleMemory,
            },
            QuotientIdentity,
        },
    },
    shape_corpus::{curated_cases, shape_fuzz_params, ShapeFuzzCircuit},
    SolidityGenerator,
};

/// Native trace ids for the scalar values quotient expressions load.
const TRACE_THETA: u64 = 7;
const TRACE_BETA: u64 = 8;
const TRACE_GAMMA: u64 = 9;
const TRACE_Y: u64 = 10;
const TRACE_X: u64 = 11;
/// Recorded only when the circuit has trashcans (the squeeze itself is
/// unconditional natively).
const TRACE_TRASH_CHALLENGE: u64 = 12;
const TRACE_L_LAST: u64 = 19;
const TRACE_L_BLIND: u64 = 20;
const TRACE_L_0: u64 = 21;
const TRACE_INSTANCE_EVAL: u64 = 22;
const TRACE_QUOTIENT_NUMERATOR: u64 = 36;
const TRACE_USER_CHALLENGE_BASE: u64 = 1_000;

/// Decode one 32-byte big-endian native trace scalar.
fn trace_scalar(events: &BTreeMap<u64, Vec<u8>>, id: u64) -> Option<Fq> {
    let data = events.get(&id)?;
    assert_eq!(
        data.len(),
        WORD_BYTES,
        "native trace id {id} is not a 32-byte scalar"
    );
    let mut le = [0u8; WORD_BYTES];
    for (le_byte, be_byte) in le.iter_mut().zip(data.iter().rev()) {
        *le_byte = *be_byte;
    }
    Some(
        Option::<Fq>::from(Fq::from_repr(<Fq as PrimeField>::Repr::from(le)))
            .unwrap_or_else(|| panic!("native trace id {id} is not a canonical Fr scalar")),
    )
}

/// Oracle memory reconstructed from a native midnight-proofs verifier trace,
/// mapped onto the generator's PLANNED absolute memory addresses.
struct TraceBackedMemory {
    /// Absolute word address -> value, with a human label for diagnostics.
    words: BTreeMap<u32, (Fq, &'static str)>,
    /// Symbolic token -> absolute base address (from the lowering plan).
    token_bases: Vec<(u8, usize)>,
}

impl TraceBackedMemory {
    /// Map native trace events onto planned verifier memory.
    ///
    /// Windows that occur in quotient expressions and their sources:
    /// * decoded proof evals: ids `20_000 + n` (the first `num_evals` proof
    ///   scalar reads — the native counter keeps counting into the PCS q_evals,
    ///   which are ignored here) land at `reversed_evals_mptr + n * 32`,
    ///   matching the transcript spill loop.
    /// * user challenges: ids `1_000 + i` land at `challenge_mptr +
    ///   challenge_indices[i] * 32` (phase-packed remap, mirroring
    ///   `Data::new`).
    /// * common slots (theta/beta/gamma/x/trash/l_0/l_last/l_blind/
    ///   instance_eval): challenge and Lagrange trace ids land at the plan's
    ///   token base addresses.
    fn from_events(events: &BTreeMap<u64, Vec<u8>>, plan: &LoweringPlan) -> Result<Self, String> {
        let mut words: BTreeMap<u32, (Fq, &'static str)> = BTreeMap::new();
        let mut insert = |addr: usize, value: Option<Fq>, label: &'static str| {
            if let Some(value) = value {
                let addr = u32::try_from(addr).expect("planned address fits in u32");
                words.insert(addr, (value, label));
            }
        };

        // Decoded proof evals (main block including fewer-point-sets dummies).
        let eval_base = plan.data.reversed_evals_mptr.value().as_usize();
        for n in 0..plan.meta.num_evals() {
            let id = trace::PROOF_EVAL_BASE as u64 + n as u64;
            let value = trace_scalar(events, id)
                .ok_or_else(|| format!("native trace is missing proof eval id {id} (slot {n})"))?;
            insert(
                eval_base + n * WORD_BYTES,
                Some(value),
                "decoded proof eval",
            );
        }

        // User challenges, phase-packed like `Data::new`.
        let challenge_base = plan.data.challenge_mptr.value().as_usize();
        for (i, &packed_index) in plan.meta.protocol.challenge_indices.iter().enumerate() {
            let id = TRACE_USER_CHALLENGE_BASE + i as u64;
            let value = trace_scalar(events, id)
                .ok_or_else(|| format!("native trace is missing user challenge id {id}"))?;
            insert(
                challenge_base + packed_index * WORD_BYTES,
                Some(value),
                "user challenge",
            );
        }

        // Common challenge/Lagrange slots at the planned token bases.
        let token_bases = plan.quotient_read_model().token_bases;
        let base_of = |token: u8| -> usize {
            token_bases
                .iter()
                .find_map(|(candidate, base)| (*candidate == token).then_some(*base))
                .unwrap_or_else(|| panic!("plan has no base for memory token {token:#x}"))
        };
        use crate::lowering::quotient_numerator::vm::{
            Q_MEM_BETA, Q_MEM_GAMMA, Q_MEM_INSTANCE_EVAL, Q_MEM_L0, Q_MEM_L_BLIND, Q_MEM_L_LAST,
            Q_MEM_THETA, Q_MEM_TRASH_CHALLENGE, Q_MEM_X,
        };
        insert(
            base_of(Q_MEM_THETA),
            trace_scalar(events, TRACE_THETA),
            "theta",
        );
        insert(
            base_of(Q_MEM_BETA),
            trace_scalar(events, TRACE_BETA),
            "beta",
        );
        insert(
            base_of(Q_MEM_GAMMA),
            trace_scalar(events, TRACE_GAMMA),
            "gamma",
        );
        insert(base_of(Q_MEM_X), trace_scalar(events, TRACE_X), "x");
        // Absent (not an error) when the circuit has no trashcans: the native
        // squeeze is unconditional but the trace records id 12 only when
        // trash identities exist, and only those identities reference it.
        insert(
            base_of(Q_MEM_TRASH_CHALLENGE),
            trace_scalar(events, TRACE_TRASH_CHALLENGE),
            "trash challenge",
        );
        insert(
            base_of(Q_MEM_L_LAST),
            trace_scalar(events, TRACE_L_LAST),
            "l_last",
        );
        insert(
            base_of(Q_MEM_L_BLIND),
            trace_scalar(events, TRACE_L_BLIND),
            "l_blind",
        );
        insert(base_of(Q_MEM_L0), trace_scalar(events, TRACE_L_0), "l_0");
        insert(
            base_of(Q_MEM_INSTANCE_EVAL),
            trace_scalar(events, TRACE_INSTANCE_EVAL),
            "instance_eval",
        );

        Ok(Self { words, token_bases })
    }
}

impl QuotientOracleMemory for TraceBackedMemory {
    fn load(&mut self, ptr: u32) -> Fq {
        if let Some((value, _)) = self.words.get(&ptr) {
            return *value;
        }
        let below = self.words.range(..ptr).next_back();
        let above = self.words.range(ptr..).next();
        panic!(
            "quotient expression loads unmapped address {ptr:#x}; nearest mapped: \
             below {:?}, above {:?}",
            below.map(|(addr, (_, label))| (format!("{addr:#x}"), *label)),
            above.map(|(addr, (_, label))| (format!("{addr:#x}"), *label)),
        );
    }

    fn token(&mut self, token: u8, offset: u32) -> Fq {
        let base = self
            .token_bases
            .iter()
            .find_map(|(candidate, base)| (*candidate == token).then_some(*base))
            .unwrap_or_else(|| panic!("no base for memory token {token:#x}"));
        let base = u32::try_from(base).expect("token base fits in u32");
        self.load(base + offset)
    }
}

/// Prove one circuit, run the traced native verifier, return its trace.
fn prove_and_trace<C: Circuit<Fq>>(
    context: &str,
    params: &ParamsKZG<Bls12>,
    pk: &midnight_proofs::plonk::ProvingKey<Fq, KZGCommitmentScheme<Bls12>>,
    circuit: &C,
    committed: &[Fq],
    public: &[Fq],
    seed: u64,
) -> BTreeMap<u64, Vec<u8>> {
    let all_instance_columns: [&[Fq]; 2] = [committed, public];
    let mut proof_rng = ChaCha8Rng::seed_from_u64(seed ^ 0x51d1_f1ed);
    let mut transcript = CircuitTranscript::<sha3::Keccak256>::init();
    create_proof::<Fq, KZGCommitmentScheme<Bls12>, _, _>(
        params,
        pk,
        std::slice::from_ref(circuit),
        1,
        &[&all_instance_columns],
        &mut proof_rng,
        &mut transcript,
    )
    .unwrap_or_else(|err| panic!("{context}: proof generation failed: {err:?}"));
    let compressed_proof = transcript.finalize();

    solidity_trace::start();
    let committed_pi = [G1Projective::identity()];
    let public_columns: [&[Fq]; 1] = [public];
    let mut verify_transcript =
        CircuitTranscript::<sha3::Keccak256>::init_from_bytes(&compressed_proof);
    let guard = prepare::<Fq, KZGCommitmentScheme<Bls12>, CircuitTranscript<sha3::Keccak256>>(
        pk.get_vk(),
        &[&committed_pi],
        &[&public_columns],
        &mut verify_transcript,
    )
    .unwrap_or_else(|err| panic!("{context}: native prepare failed: {err:?}"));
    verify_transcript
        .assert_empty()
        .unwrap_or_else(|_| panic!("{context}: transcript had trailing bytes"));
    guard
        .verify(&params.verifier_params())
        .unwrap_or_else(|err| panic!("{context}: native pairing failed: {err:?}"));
    let events: Vec<SolidityTraceEvent> = solidity_trace::take();

    let mut by_id = BTreeMap::new();
    for event in events {
        assert!(
            by_id.insert(event.id, event.data).is_none(),
            "{context}: duplicate native trace id {}",
            event.id
        );
    }
    by_id
}

/// Compare every planned identity expression, the y-batched numerator, and
/// the selector folds against the native trace.
fn assert_anchor(
    context: &str,
    generator: &SolidityGenerator<'_>,
    events: &BTreeMap<u64, Vec<u8>>,
) {
    let plan = generator.plan().unwrap_or_else(|err| panic!("{context}: plan failed: {err}"));

    let mut identities: Vec<&QuotientIdentity> = plan
        .quotient
        .plan
        .identities_in_execution_order()
        .unwrap_or_else(|err| panic!("{context}: execution walk failed: {err}"))
        .into_iter()
        .map(|(identity, _)| identity)
        .collect();
    identities.sort_by_key(|identity| identity.meta.global_index);

    let native_identity_count = events
        .keys()
        .filter(|id| (trace::QUOTIENT_IDENTITY_BASE..trace::PCS_Q_COM_BASE).contains(id))
        .count();
    assert_eq!(
        identities.len(),
        native_identity_count,
        "{context}: generator plans {} identities, native verifier traced {}",
        identities.len(),
        native_identity_count
    );

    let mut mem = TraceBackedMemory::from_events(events, plan)
        .unwrap_or_else(|err| panic!("{context}: trace-backed memory failed: {err}"));

    for identity in &identities {
        let global_index = identity.meta.global_index;
        let value = eval_quotient_expr_with(&identity.expr, &mut mem);
        let native = trace_scalar(events, trace::QUOTIENT_IDENTITY_BASE + global_index as u64)
            .unwrap_or_else(|| panic!("{context}: native trace missing identity {global_index}"));
        assert_eq!(
            value, native,
            "{context}: identity {global_index} ({:?}) diverges from the native verifier",
            identity.meta.source
        );
    }

    // The y-batched numerator and every selector bucket, pinning fold order
    // and the per-bucket assignment (the trace ids are positional).
    let y = trace_scalar(events, TRACE_Y)
        .unwrap_or_else(|| panic!("{context}: native trace missing y"));
    let owned: Vec<QuotientIdentity> = identities.into_iter().cloned().collect();
    let selector_count = plan.quotient.sorted_simple.len();
    let artifacts = expected_linearization_artifacts(&owned, &mut mem, y, selector_count);
    let native_numerator = trace_scalar(events, TRACE_QUOTIENT_NUMERATOR)
        .unwrap_or_else(|| panic!("{context}: native trace missing quotient numerator"));
    assert_eq!(
        artifacts.main_numerator, native_numerator,
        "{context}: y-batched numerator diverges from the native verifier"
    );
    for bucket in 0..selector_count {
        let native_fold = trace_scalar(events, trace::SELECTOR_FOLD_BASE as u64 + bucket as u64)
            .unwrap_or_else(|| panic!("{context}: native trace missing selector fold {bucket}"));
        assert_eq!(
            artifacts.selector_buckets[bucket], native_fold,
            "{context}: selector bucket {bucket} diverges from the native verifier"
        );
    }
    let native_fold_count = events
        .keys()
        .filter(|id| (trace::SELECTOR_FOLD_BASE as u64..61_000).contains(id))
        .count();
    assert_eq!(
        selector_count, native_fold_count,
        "{context}: selector bucket count diverges from the native trace"
    );
}

/// Corpus cases chosen for family diversity: permutation (incl. multi-set
/// delta walk), LogUp (incl. helper chunk splits), trash, seven-limb
/// recognizer shapes, and selector buckets with gaps.
///
/// The tier-1 VK circuits (`quotient_vm_test_vk`/`quotient_selector_fold_
/// test_vk`) are deliberately absent: their ungated advice constraints
/// cannot vanish on the real prover's blinding rows (MockProver-only by
/// design), which is exactly why the shape corpus carries provable
/// fixed-column variants of the same recognizer/selector shapes -- the
/// `seven-limb foreign-field vm overflow` and `selector bucket gaps
/// interleaved pow5` cases below.
const ANCHOR_CASES: [&str; 6] = [
    "next-rotation permutation",
    "second-phase lookup",
    "trash-additive selector with lookup",
    "degree-6 wide-permutation delta walk",
    "seven-limb foreign-field vm overflow",
    "selector bucket gaps interleaved pow5",
];

#[test]
fn native_anchor_matches_per_identity_trace() {
    for case in curated_cases() {
        if !ANCHOR_CASES.contains(&case.name) {
            continue;
        }
        let context = format!("native anchor `{}`", case.name);
        let circuit = ShapeFuzzCircuit::new(case.spec, case.seed);
        let mut setup_rng = ChaCha8Rng::seed_from_u64(case.seed ^ 0x7ace_f00d);
        let params = shape_fuzz_params(&[(case.spec, case.k)], &mut setup_rng);
        let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, case.k)
            .unwrap_or_else(|err| panic!("{context}: vk generation failed: {err:?}"));
        let pk = keygen_pk(vk, &circuit)
            .unwrap_or_else(|err| panic!("{context}: pk generation failed: {err:?}"));
        let committed = [Fq::ZERO];
        let public = [circuit.public_instance()];
        let events = prove_and_trace(
            &context, &params, &pk, &circuit, &committed, &public, case.seed,
        );
        let generator = SolidityGenerator::new(&params, pk.get_vk(), GeneratorConfig::new(1, 1));
        assert_anchor(&context, &generator, &events);
    }
}
