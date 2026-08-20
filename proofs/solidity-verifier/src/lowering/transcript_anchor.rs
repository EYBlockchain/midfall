// SPDX-License-Identifier: CC0-1.0
//! Native anchor for the generator's proof-read plan (roadmap P6.b).
//!
//! `ProtocolPlan.proof` decides the calldata layout, the off-chain repacker's
//! walk, and the rendered transcript loop counts, but nothing compared it
//! against what the native verifier actually reads -- the Solidity trace
//! differential does, yet it needs solc, revm, a real proving run, and the
//! `rust-verifier-trace` feature.
//!
//! This anchors the same fact with none of that. It implements
//! midnight-proofs' public [`Transcript`] trait over the real
//! `CircuitTranscript`, records every `read`/`common`/`squeeze` the verifier
//! performs, and drives the real `prepare` over a proof SYNTHESIZED from the
//! generator's own plan. The interleaving is produced by native control flow
//! (`plonk::verifier`'s phase loops and `poly::kzg`'s multi-open), so a plan
//! that disagrees about how many commitments or evaluations the proof carries,
//! or in what order, desynchronizes and fails here.
//!
//! No proving, no solc, no features: this runs in every CI matrix combination,
//! including the default one where `truncated-challenges` is off.

use std::io;

use ff::PrimeField;
use group::{prime::PrimeCurveAffine, Group, GroupEncoding};
use midnight_curves::{Bls12, Fq, G1Affine, G1Projective};
use midnight_proofs::{
    plonk::{keygen_vk_with_k, prepare},
    poly::kzg::KZGCommitmentScheme,
    transcript::{CircuitTranscript, Hashable, Sampleable, Transcript},
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::{
    api::GeneratorConfig,
    lowering::quotient_numerator::vm::RepackedProofLayoutPlan,
    shape_corpus::{curated_cases, shape_fuzz_params, ShapeFuzzCircuit},
    SolidityGenerator,
};

/// Wire size of a compressed G1 commitment in a native proof.
const G1_WIRE_BYTES: usize = 48;
/// Wire size of a scalar evaluation in a native proof.
const SCALAR_WIRE_BYTES: usize = 32;

/// Fixed challenges every proof squeezes, in verifier order: theta, beta,
/// gamma, the trash challenge (squeezed unconditionally, even with no trash
/// arguments), y, x, then the multi-open's x1, x2, x3, x4.
const FIXED_CHALLENGES: usize = 10;

/// One transcript operation observed on the native verifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TranscriptOp {
    /// A value both sides already know, absorbed without consuming the proof.
    Absorb {
        /// Byte length of the hash input (32 for a scalar, 128 for a G1).
        bytes: usize,
    },
    /// A proof element consumed from the wire and absorbed.
    Read {
        /// Byte length consumed from the proof (48 compressed G1, 32 scalar).
        wire: usize,
    },
    /// A Fiat-Shamir challenge squeeze.
    Squeeze,
}

/// A `Transcript` that records what the verifier does while delegating to the
/// real one, so the observed schedule is the native schedule.
#[derive(Clone, Debug)]
pub(crate) struct RecordingTranscript {
    /// The genuine transcript; all hashing happens here.
    inner: CircuitTranscript<sha3::Keccak256>,
    /// Operations in the order the verifier performed them.
    ops: Vec<TranscriptOp>,
}

impl RecordingTranscript {
    /// Proof-element reads, in order.
    fn reads(&self) -> Vec<usize> {
        self.ops
            .iter()
            .filter_map(|op| match op {
                TranscriptOp::Read { wire } => Some(*wire),
                _ => None,
            })
            .collect()
    }

    /// Number of challenges squeezed.
    fn squeezes(&self) -> usize {
        self.ops.iter().filter(|op| matches!(op, TranscriptOp::Squeeze)).count()
    }
}

impl Transcript for RecordingTranscript {
    /// Same hash as the production transcript.
    type Hash = sha3::Keccak256;

    /// Start an empty recording transcript.
    fn init() -> Self {
        Self {
            inner: CircuitTranscript::init(),
            ops: Vec::new(),
        }
    }

    /// Start from proof bytes, recording nothing yet.
    fn init_from_bytes(bytes: &[u8]) -> Self {
        Self {
            inner: CircuitTranscript::init_from_bytes(bytes),
            ops: Vec::new(),
        }
    }

    /// Record and delegate a challenge squeeze.
    fn squeeze_challenge<T: Sampleable<Self::Hash>>(&mut self) -> T {
        self.ops.push(TranscriptOp::Squeeze);
        self.inner.squeeze_challenge()
    }

    /// Record and delegate an absorb of already-known data.
    ///
    /// The recorded size is the HASH input width (`to_input`), not the wire
    /// width: a G1 absorbed as a common value contributes its 128-byte
    /// EIP-2537 form.
    fn common<T: Hashable<Self::Hash>>(&mut self, input: &T) -> io::Result<()> {
        self.ops.push(TranscriptOp::Absorb {
            bytes: input.to_input().len(),
        });
        self.inner.common(input)
    }

    /// Record and delegate a proof read.
    ///
    /// `CircuitTranscript::read` consumes from the buffer and then absorbs, so
    /// the wire width is the cursor delta. Recording it as one `Read` (rather
    /// than a read plus the absorb it performs internally) keeps the log in
    /// terms of proof structure.
    fn read<T: Hashable<Self::Hash>>(&mut self) -> io::Result<T> {
        let before = self.inner.buffer().position();
        let value = self.inner.read::<T>()?;
        let wire = (self.inner.buffer().position() - before) as usize;
        self.ops.push(TranscriptOp::Read { wire });
        Ok(value)
    }

    /// Delegate; the verifier never writes.
    fn write<T: Hashable<Self::Hash>>(&mut self, input: &T) -> io::Result<()> {
        self.inner.write(input)
    }

    /// Delegate.
    fn finalize(self) -> Vec<u8> {
        self.inner.finalize()
    }

    /// Delegate: used to prove the synthetic proof was consumed exactly.
    fn assert_empty(&mut self) -> io::Result<()> {
        self.inner.assert_empty()
    }
}

/// Build proof bytes in exactly the shape the generator's plan describes.
///
/// Commitments are the compressed generator point and evaluations are small
/// canonical scalars: `prepare` parses and prepares, deciding validity only at
/// the final pairing, so structurally well-formed bytes are enough -- and the
/// point is to test the SHAPE, which is what the plan claims.
fn synthesize_proof(plan: &RepackedProofLayoutPlan) -> Vec<u8> {
    let point = G1Affine::generator().to_bytes();
    let mut out = Vec::with_capacity(plan.compressed_len());
    let push_scalar = |out: &mut Vec<u8>, index: usize| {
        let value = Fq::from(index as u64 + 1);
        out.extend_from_slice(value.to_repr().as_ref());
    };

    for &count in &plan.g1_groups {
        for _ in 0..count {
            out.extend_from_slice(point.as_ref());
        }
    }
    for index in 0..plan.num_evals {
        push_scalar(&mut out, index);
    }
    out.extend_from_slice(point.as_ref()); // f_com
    for index in 0..plan.num_point_sets {
        push_scalar(&mut out, plan.num_evals + index);
    }
    out.extend_from_slice(point.as_ref()); // pi

    assert_eq!(
        out.len(),
        plan.compressed_len(),
        "synthetic proof length must match the plan's own compressed length"
    );
    out
}

/// The read sequence the plan claims the proof carries.
fn planned_reads(plan: &RepackedProofLayoutPlan) -> Vec<usize> {
    let mut reads = Vec::new();
    for &count in &plan.g1_groups {
        reads.extend(std::iter::repeat_n(G1_WIRE_BYTES, count));
    }
    reads.extend(std::iter::repeat_n(SCALAR_WIRE_BYTES, plan.num_evals));
    reads.push(G1_WIRE_BYTES); // f_com
    reads.extend(std::iter::repeat_n(SCALAR_WIRE_BYTES, plan.num_point_sets));
    reads.push(G1_WIRE_BYTES); // pi
    reads
}

/// Drive the native verifier over a plan-shaped proof and compare schedules.
#[test]
fn proof_read_plan_matches_native_verifier_schedule() {
    let mut setup_rng = ChaCha8Rng::seed_from_u64(0x7a5c_0de1);
    let mut checked = 0usize;

    for case in curated_cases() {
        let context = format!("transcript anchor `{}`", case.name);
        let circuit = ShapeFuzzCircuit::new(case.spec, case.seed);
        let params = shape_fuzz_params(&[(case.spec, case.k)], &mut setup_rng);
        let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, case.k)
            .unwrap_or_else(|err| panic!("{context}: vk generation failed: {err:?}"));

        let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
        let plan = generator.inputs().lowering_plan();
        let repack = plan.repacked_proof_layout_plan();

        let proof = synthesize_proof(&repack);
        let committed_pi = [G1Projective::identity()];
        let public = [circuit.public_instance()];
        let public_columns: [&[Fq]; 1] = [&public];
        let mut transcript = RecordingTranscript::init_from_bytes(&proof);
        prepare::<Fq, KZGCommitmentScheme<Bls12>, RecordingTranscript>(
            &vk,
            &[&committed_pi],
            &[&public_columns],
            &mut transcript,
        )
        .unwrap_or_else(|err| {
            panic!(
                "{context}: native prepare rejected a proof shaped by the generator's own \
                 plan ({} commitments, {} evals, {} point sets): {err:?}",
                repack.prefix_g1_count(),
                repack.num_evals,
                repack.num_point_sets
            )
        });

        // Every byte the plan claimed was consumed, and no more. Under- or
        // over-counting shows up here even when the op sequence happens to
        // line up on a prefix.
        transcript
            .assert_empty()
            .unwrap_or_else(|_| panic!("{context}: native verifier left proof bytes unread"));

        assert_eq!(
            transcript.reads(),
            planned_reads(&repack),
            "{context}: the native verifier's proof-read sequence diverges from the \
             generator's plan (which drives the calldata layout, the repacker walk, \
             and the rendered transcript loops)"
        );

        let expected_squeezes =
            FIXED_CHALLENGES + plan.meta.protocol.num_user_challenges.iter().sum::<usize>();
        assert_eq!(
            transcript.squeezes(),
            expected_squeezes,
            "{context}: challenge count diverges from the generated schedule"
        );

        checked += 1;
    }

    assert_eq!(
        checked,
        curated_cases().len(),
        "every corpus case must be anchored"
    );
}
