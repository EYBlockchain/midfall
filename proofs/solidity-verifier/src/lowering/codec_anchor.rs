// SPDX-License-Identifier: CC0-1.0
//! Native anchors for the G1 wire codecs (roadmap P7).
//!
//! A proof carries commitments 48-byte ZCash-compressed; the generated
//! verifier consumes them as 128-byte EIP-2537 words, and the native verifier
//! hashes exactly that 128-byte form (`Hashable::to_input`). Two independent
//! pieces of this crate must therefore produce it byte-for-byte:
//!
//!   * [`crate::lowering::encoding::g1_to_u256s`], which bakes VK commitments
//!     into the generated payload, and
//!   * the off-chain repacker (`VerifierBuildInputs::repack_proof`), which
//!     rewrites proof commitments into calldata.
//!
//! Both were covered only end to end -- a real proof through solc and revm --
//! so no test pinned either against the native encoding, and none exercised
//! the identity or coordinate-boundary cases at all. A divergence here does
//! not forge proofs (the transcripts simply stop matching and honest proofs
//! are rejected), but it is silent until a full EVM run and it would be
//! invisible for point classes the fixtures happen not to contain.

use ff::PrimeField;
use group::{prime::PrimeCurveAffine, Curve, Group, GroupEncoding};
use midnight_curves::{Bls12, Fq, G1Affine, G1Projective};
use midnight_proofs::{
    plonk::keygen_vk_with_k, poly::kzg::KZGCommitmentScheme, transcript::Hashable,
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use crate::{
    api::GeneratorConfig,
    lowering::{encoding::g1_to_u256s, layout::G1_COMPRESSED_BYTES},
    shape_corpus::{curated_cases, shape_fuzz_params, ShapeFuzzCircuit},
    SolidityGenerator,
};

/// Byte width of the EIP-2537 padded G1 encoding the verifier hashes.
const G1_PADDED_BYTES: usize = 128;
/// Byte width of a scalar word.
const WORD_BYTES: usize = 32;

/// Points every G1 codec must round-trip, including the classes a fixture
/// proof is unlikely to contain.
fn codec_points() -> Vec<G1Affine> {
    let mut rng = ChaCha8Rng::seed_from_u64(0xc0de_c0de);
    let generator = G1Projective::generator();
    let mut points = vec![
        G1Affine::identity(),
        generator.to_affine(),
        (generator + generator).to_affine(),
        (-generator).to_affine(),
    ];
    points.extend((0..6).map(|_| G1Projective::random(&mut rng).to_affine()));
    points
}

/// The 128-byte form the native verifier hashes for a point.
fn native_padded(point: &G1Affine) -> Vec<u8> {
    let projective = G1Projective::from(*point);
    <G1Projective as Hashable<sha3::Keccak256>>::to_input(&projective)
}

/// The VK-side encoder must agree with the native hash input.
///
/// `g1_to_u256s` writes every fixed and permutation commitment into the
/// generated VK payload, which the verifier absorbs; if its hi/lo split
/// diverged from `to_input`, the Fiat-Shamir prefix would differ from the
/// native verifier's on the very first absorb.
#[test]
fn vk_g1_encoder_matches_native_hash_input() {
    for point in codec_points() {
        let words = g1_to_u256s(point);
        let encoded: Vec<u8> = words.iter().flat_map(|word| word.to_be_bytes::<32>()).collect();
        assert_eq!(
            encoded.len(),
            G1_PADDED_BYTES,
            "EIP-2537 G1 encoding must be four words"
        );
        assert_eq!(
            encoded,
            native_padded(&point),
            "g1_to_u256s diverges from the native verifier's hash input for {point:?}"
        );
    }
}

/// The proof repacker must agree with the native hash input, for every G1 in
/// a real generated proof layout.
///
/// This drives the production `repack_proof` over a proof synthesized in the
/// shape the generator's own plan describes, cycling the commitment slots
/// through the edge-case points, then checks each 128-byte calldata window
/// against the native encoding. The identity is included deliberately: the
/// repacker takes a dedicated branch for it.
#[test]
fn proof_repacker_matches_native_hash_input() {
    let case = curated_cases()
        .into_iter()
        .find(|case| case.name == "full mixed lookup permutation shape")
        .expect("corpus carries the mixed shape");
    let mut setup_rng = ChaCha8Rng::seed_from_u64(0xc0de_a11c);
    let circuit = ShapeFuzzCircuit::new(case.spec, case.seed);
    let params = shape_fuzz_params(&[(case.spec, case.k)], &mut setup_rng);
    let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, case.k)
        .expect("vk generation");
    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    let plan = generator.inputs().lowering_plan();
    let repack = plan.repacked_proof_layout_plan();

    // Every G1 slot in the proof, in wire order: the commitment prefix, then
    // f_com and pi after the evaluation blocks.
    let points = codec_points();
    let total_g1 = repack.prefix_g1_count() + 2;
    let chosen: Vec<G1Affine> = (0..total_g1).map(|idx| points[idx % points.len()]).collect();

    let mut proof = Vec::with_capacity(repack.compressed_len());
    let mut next = chosen.iter();
    let push_point = |proof: &mut Vec<u8>, point: &G1Affine| {
        proof.extend_from_slice(point.to_bytes().as_ref());
    };
    for &count in &repack.g1_groups {
        for _ in 0..count {
            push_point(&mut proof, next.next().expect("a point per commitment"));
        }
    }
    for index in 0..repack.num_evals {
        proof.extend_from_slice(Fq::from(index as u64 + 1).to_repr().as_ref());
    }
    push_point(&mut proof, next.next().expect("f_com point")); // f_com
    for index in 0..repack.num_point_sets {
        proof.extend_from_slice(Fq::from(index as u64 + 1).to_repr().as_ref());
    }
    push_point(&mut proof, next.next().expect("pi point")); // pi
    assert_eq!(
        proof.len(),
        repack.compressed_len(),
        "synthetic proof length"
    );
    assert_eq!(
        G1_COMPRESSED_BYTES * total_g1 + WORD_BYTES * (repack.num_evals + repack.num_point_sets),
        proof.len(),
        "synthetic proof is commitments plus scalars only"
    );

    let calldata = generator.repack_proof(&proof).expect("repack");

    // Commitment prefix.
    for (idx, point) in chosen.iter().take(repack.prefix_g1_count()).enumerate() {
        let start = idx * G1_PADDED_BYTES;
        assert_eq!(
            &calldata[start..start + G1_PADDED_BYTES],
            native_padded(point).as_slice(),
            "repacked commitment {idx} diverges from the native verifier's hash input"
        );
    }

    // f_com and pi sit after the eval block and the q_eval block respectively.
    let f_com_start = repack.prefix_g1_count() * G1_PADDED_BYTES + repack.num_evals * WORD_BYTES;
    assert_eq!(
        &calldata[f_com_start..f_com_start + G1_PADDED_BYTES],
        native_padded(&chosen[repack.prefix_g1_count()]).as_slice(),
        "repacked f_com diverges from the native verifier's hash input"
    );
    let pi_start = f_com_start + G1_PADDED_BYTES + repack.num_point_sets * WORD_BYTES;
    assert_eq!(
        &calldata[pi_start..pi_start + G1_PADDED_BYTES],
        native_padded(&chosen[repack.prefix_g1_count() + 1]).as_slice(),
        "repacked pi diverges from the native verifier's hash input"
    );
    assert_eq!(
        calldata.len(),
        pi_start + G1_PADDED_BYTES,
        "repacked calldata carries exactly the planned elements"
    );
}
