use std::{
    hash::Hash,
    iter::{self},
};

use ff::{FromUniformBytes, WithSmallOrderMulGroup};

use super::{Error, VerifyingKey};
use crate::{
    plonk::{
        linearization::verifier::compute_linearization_commitment, partially_evaluate_identities,
        traces::VerifierTrace,
    },
    poly::{commitment::PolynomialCommitmentScheme, CommitmentLabel, VerifierQuery},
    transcript::{read_n, Hashable, Sampleable, Transcript, TranscriptInputBytes},
    utils::arithmetic::compute_inner_product,
};

/// Given a plonk proof, this function parses it to extract the verifying trace.
/// This function computes all Fiat-Shamir challenges, with the exception of
/// `x`, which is computed in [verify_algebraic_constraints]
pub fn parse_trace<F, CS, T>(
    vk: &VerifyingKey<F, CS>,
    // Unlike the prover, the verifier gets their instances in two arguments:
    // committed and normal (non-committed). Note that the total number of
    // instance columns is expected to be the sum of committed instances and
    // normal instances for every proof. (Committed instances go first, that is,
    // the first instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
    instances: &[&[&[F]]],
    transcript: &mut T,
) -> Result<VerifierTrace<F, CS>, Error>
where
    CS: PolynomialCommitmentScheme<F>,
    T: Transcript,
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Ord,
    CS::Commitment: Hashable<T::Hash>,
    <T::Hash as crate::transcript::TranscriptHash>::Input: TranscriptInputBytes,
{
    #[cfg(not(feature = "committed-instances"))]
    let committed_instances: Vec<Vec<CS::Commitment>> = vec![vec![]; instances.len()];

    if committed_instances.is_empty() {
        return Err(Error::InvalidInstances);
    }

    let nb_committed_instances = committed_instances[0].len();
    for committed_instances in committed_instances.iter() {
        if committed_instances.len() != nb_committed_instances {
            return Err(Error::InvalidInstances);
        }
    }

    // Check that instances matches the expected number of instance columns
    for (committed_instances, instances) in committed_instances.iter().zip(instances.iter()) {
        if committed_instances.len() + instances.len() != vk.cs.num_instance_columns {
            return Err(Error::InvalidInstances);
        }
    }

    let num_proofs = instances.len();

    // Hash verification key into transcript
    vk.hash_into(transcript)?;
    #[cfg(feature = "solidity-verifier-trace")]
    {
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
            1,
            "vk_digest",
            &vk.transcript_repr(),
        );
        let num_instances = instances
            .first()
            .and_then(|cols| cols.first())
            .map(|values| values.len())
            .unwrap_or_default();
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
            2,
            "num_instances",
            &F::from_u128(num_instances as u128),
        );
    }

    for committed_instances in committed_instances.iter() {
        for commitment in committed_instances.iter() {
            transcript.common(commitment)?
        }
    }

    for instance in instances.iter() {
        for instance in instance.iter() {
            transcript.common(&F::from_u128(instance.len() as u128))?;
            for value in instance.iter() {
                transcript.common(value)?;
            }
        }
    }

    // Hash the prover's advice commitments into the transcript and squeeze
    // challenges
    let (advice_commitments, challenges) = {
        let mut advice_commitments =
            vec![vec![CS::Commitment::default(); vk.cs.num_advice_columns]; num_proofs];
        let mut challenges = vec![F::ZERO; vk.cs.num_challenges];

        for current_phase in vk.cs.phases() {
            for advice_commitments in advice_commitments.iter_mut() {
                for (phase, commitment) in
                    vk.cs.advice_column_phase.iter().zip(advice_commitments.iter_mut())
                {
                    if current_phase == *phase {
                        *commitment = transcript.read()?;
                        #[cfg(feature = "solidity-verifier-trace")]
                        crate::plonk::solidity_trace::record_proof_commitment::<T::Hash, _>(
                            "proof_advice_commitment",
                            &*commitment,
                        );
                    }
                }
            }
            for (phase, challenge) in vk.cs.challenge_phase.iter().zip(challenges.iter_mut()) {
                if current_phase == *phase {
                    *challenge = transcript.squeeze_challenge();
                }
            }
        }

        (advice_commitments, challenges)
    };

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: F = transcript.squeeze_challenge();
    #[cfg(feature = "solidity-verifier-trace")]
    crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(7, "theta", &theta);

    // Read multiplicities
    let lookup_multiplicities = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            // Hash each lookup permuted commitment
            vk.cs
                .lookups
                .iter()
                .map(|l| l.chunk_by_degree(vk.cs_degree).read_multiplicities::<_, CS>(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Sample beta challenge
    let beta: F = transcript.squeeze_challenge();
    #[cfg(feature = "solidity-verifier-trace")]
    crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(8, "beta", &beta);

    // Sample gamma challenge
    let gamma: F = transcript.squeeze_challenge();
    #[cfg(feature = "solidity-verifier-trace")]
    crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(9, "gamma", &gamma);

    let permutations_committed = (0..num_proofs)
        .map(|_| {
            // Hash each permutation product commitment
            vk.cs.permutation.read_product_commitments(vk, transcript)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let lookups_committed = lookup_multiplicities
        .into_iter()
        .map(|lookups| {
            lookups
                .into_iter()
                .zip(vk.cs.lookups.iter().map(|l| l.chunk_by_degree(vk.cs_degree)))
                .map(|(m, batch)| m.read_commitment(batch.num_chunks(), transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    let trash_challenge: F = transcript.squeeze_challenge();

    let trashcans_committed = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            vk.cs
                .trashcans
                .iter()
                .map(|argument| argument.read_committed::<CS, _>(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Sample y challenge, which keeps the gates linearly independent.
    let y: F = transcript.squeeze_challenge();
    #[cfg(feature = "solidity-verifier-trace")]
    crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(10, "y", &y);

    Ok(VerifierTrace {
        advice_commitments,
        lookups: lookups_committed,
        trashcans: trashcans_committed,
        permutations: permutations_committed,
        challenges,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
    })
}

/// Given a VerifierTrace, this function computes the opening challenge, x,
/// and proceeds to verify the algebraic constraints with the claimed
/// evaluations. This function does not verify the PCS proof.
///
/// The verifier will error if there are trailing bits in the transcript.
pub fn verify_algebraic_constraints<F, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
    vk: &VerifyingKey<F, CS>,
    trace: VerifierTrace<F, CS>,
    // Unlike the prover, the verifier gets their instances in two arguments:
    // committed and normal (non-committed). Note that the total number of
    // instance columns is expected to be the sum of committed instances and
    // normal instances for every proof. (Committed instances go first, that is,
    // the first instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
    instances: &[&[&[F]]],
    transcript: &mut T,
) -> Result<CS::VerificationGuard, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Hash
        + Ord,
    CS::Commitment: Hashable<T::Hash>,
    <T::Hash as crate::transcript::TranscriptHash>::Input: TranscriptInputBytes,
{
    #[cfg(not(feature = "committed-instances"))]
    let committed_instances: Vec<Vec<CS::Commitment>> = vec![vec![]; instances.len()];

    if committed_instances.is_empty() {
        return Err(Error::InvalidInstances);
    }

    let nb_committed_instances = committed_instances[0].len();
    let num_proofs = instances.len();

    let VerifierTrace {
        advice_commitments,
        lookups,
        trashcans,
        permutations,
        challenges,
        beta,
        gamma,
        theta,
        trash_challenge,
        y,
    } = trace;

    // Read commitment(s) to the quotient polynomial h(X) = nu(X)/(X^n-1) from
    // the transcript. When the `single-h-commitment` feature is enabled the prover
    // commits to h(X) as a single polynomial (one commitment); otherwise it
    // splits h(X) into `quotient_poly_degree` limbs (one commitment each).
    #[cfg(not(feature = "single-h-commitment"))]
    let nb_quotient_coms = vk.domain.get_quotient_poly_degree();
    #[cfg(feature = "single-h-commitment")]
    let nb_quotient_coms = 1;
    let quotient_limb_coms = read_n(transcript, nb_quotient_coms)?;
    #[cfg(feature = "solidity-verifier-trace")]
    {
        for commitment in &quotient_limb_coms {
            crate::plonk::solidity_trace::record_proof_commitment::<T::Hash, _>(
                "proof_quotient_commitment",
                commitment,
            );
        }
    }

    // Sample x challenge, which is used to ensure the circuit is
    // satisfied with high probability.
    let x: F = transcript.squeeze_challenge();
    #[cfg(feature = "solidity-verifier-trace")]
    {
        crate::plonk::solidity_trace::record_u64(3, "k", vk.get_domain().k() as u64);
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
            4,
            "n_inv",
            &F::from(vk.n()).invert().unwrap(),
        );
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
            5,
            "omega",
            &vk.get_domain().get_omega(),
        );
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
            6,
            "omega_inv",
            &vk.get_domain().get_omega_inv(),
        );
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(11, "x", &x);
    }

    let splitting_factor = x.pow_vartime([vk.n() - 1]);
    let xn = splitting_factor * x;

    let instance_evals = {
        let (min_rotation, max_rotation) =
            vk.cs.instance_queries.iter().fold((0, 0), |(min, max), (_, rotation)| {
                if rotation.0 < min {
                    (rotation.0, max)
                } else if rotation.0 > max {
                    (min, rotation.0)
                } else {
                    (min, max)
                }
            });
        let max_instance_len = instances
            .iter()
            .flat_map(|instance| instance.iter().map(|instance| instance.len()))
            .max_by(Ord::cmp)
            .unwrap_or_default();
        let l_i_s = &vk.domain.l_i_range(
            x,
            xn,
            -max_rotation..max_instance_len as i32 + min_rotation.abs(),
        );
        instances
            .iter()
            .map(|instances| {
                vk.cs
                    .instance_queries
                    .iter()
                    .map(|(column, rotation)| {
                        if column.index() < nb_committed_instances {
                            let eval = transcript.read()?;
                            #[cfg(feature = "solidity-verifier-trace")]
                            crate::plonk::solidity_trace::record_proof_eval::<T::Hash, _>(
                                "proof_committed_instance_eval",
                                &eval,
                            );
                            Ok::<F, Error>(eval)
                        } else {
                            let instances = instances[column.index() - nb_committed_instances];
                            let offset = (max_rotation - rotation.0) as usize;
                            Ok(compute_inner_product(
                                instances,
                                &l_i_s[offset..offset + instances.len()],
                            ))
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?
    };

    let advice_evals = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            let evals = read_n(transcript, vk.cs.advice_queries.len())?;
            #[cfg(feature = "solidity-verifier-trace")]
            {
                for eval in &evals {
                    crate::plonk::solidity_trace::record_proof_eval::<T::Hash, _>(
                        "proof_advice_eval",
                        eval,
                    );
                }
            }
            Ok::<Vec<F>, Error>(evals)
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Read (num_fixed_columns - num_simple_selectors) evals and from the transcript
    // and fill up the "missing" places with 1 (the transcript doesn't contain evals
    // corresponding to multiplicative, simple selectors)
    let mut fixed_evals = read_n(
        transcript,
        vk.cs.num_fixed_columns() - vk.cs.num_simple_selectors(),
    )?;
    #[cfg(feature = "solidity-verifier-trace")]
    {
        for eval in &fixed_evals {
            crate::plonk::solidity_trace::record_proof_eval::<T::Hash, _>("proof_fixed_eval", eval);
        }
    }
    for (idx, (col, _)) in vk.cs.fixed_queries().iter().enumerate() {
        if vk.cs.has_simple_selector_col(col.index()) {
            fixed_evals.insert(idx, F::ONE)
        }
    }

    let permutations_common = vk.permutation.evaluate(transcript)?;

    let permutations_evaluated = permutations
        .into_iter()
        .map(|permutation| permutation.evaluate(transcript))
        .collect::<Result<Vec<_>, _>>()?;

    let lookups_evaluated = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            lookups
                .into_iter()
                .map(|lookup| lookup.evaluate(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    let trashcans_evaluated = trashcans
        .into_iter()
        .map(|trashcans| -> Result<Vec<_>, _> {
            trashcans
                .into_iter()
                .map(|trash| trash.evaluate(transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    #[cfg(feature = "solidity-verifier-trace")]
    {
        let blinding_factors = vk.cs.blinding_factors();
        let l_evals = vk.domain.l_i_range(x, xn, (-((blinding_factors + 1) as i32))..=0);
        assert_eq!(l_evals.len(), 2 + blinding_factors);
        let l_last = l_evals[0];
        let l_blind =
            l_evals[1..(1 + blinding_factors)].iter().fold(F::ZERO, |acc, eval| acc + eval);
        let l_0 = l_evals[1 + blinding_factors];
        let x_n_minus_1_inv = (xn - F::ONE).invert().unwrap();
        let instance_eval = vk
            .cs
            .instance_queries
            .iter()
            .position(|(column, _)| column.index() >= nb_committed_instances)
            .map(|idx| instance_evals[0][idx])
            .unwrap_or(F::ZERO);

        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(17, "x_n", &xn);
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
            18,
            "x_n_minus_1_inv",
            &x_n_minus_1_inv,
        );
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(19, "l_last", &l_last);
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(20, "l_blind", &l_blind);
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(21, "l_0", &l_0);
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
            22,
            "instance_eval",
            &instance_eval,
        );
    }

    // Partially evaluate batched identities
    // (without fixed columns corresponding to simple, multiplicative selectors)
    let expressions = partially_evaluate_identities(
        vk,
        &fixed_evals,
        &instance_evals,
        &advice_evals,
        permutations_evaluated.iter().map(|e| &e.sets),
        lookups_evaluated.iter().map(|e| e.iter().map(|inner| &inner.evaluated)),
        trashcans_evaluated.iter().map(|e| e.iter().map(|inner| &inner.evaluated)),
        &permutations_common,
        x,
        xn,
        beta,
        gamma,
        theta,
        trash_challenge,
        &challenges,
    );
    #[cfg(feature = "solidity-verifier-trace")]
    {
        for (idx, (_, eval)) in expressions.iter().enumerate() {
            crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
                crate::plonk::solidity_trace::QUOTIENT_IDENTITY_TRACE_BASE + idx as u64,
                "quotient_identity_eval",
                eval,
            );
        }
    }

    let lin_com = compute_linearization_commitment(
        expressions,
        vk,
        x,
        &y,
        &xn,
        &splitting_factor,
        &quotient_limb_coms,
    );
    #[cfg(feature = "solidity-verifier-trace")]
    {
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
            23,
            "linearization_expected_eval",
            &lin_com.eval,
        );

        let linearization_commitment = lin_com
            .commitment
            .as_terms()
            .into_iter()
            .fold(CS::Commitment::default(), |acc, (scalar, commitment)| {
                acc + commitment * scalar
            });
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
            crate::plonk::solidity_trace::LINEARIZATION_COMMITMENT_TRACE_ID,
            "linearization_commitment",
            &linearization_commitment,
        );

        let mut linearization_scalars = Vec::with_capacity(0x80);
        linearization_scalars.extend_from_slice(&splitting_factor.to_input().into_trace_bytes());
        linearization_scalars.extend_from_slice(&(F::ONE - xn).to_input().into_trace_bytes());
        linearization_scalars.extend_from_slice(&[0u8; 0x40]);
        crate::plonk::solidity_trace::record_bytes(
            24,
            "linearization_scalars",
            linearization_scalars,
        );
    }

    // Collect queries that are checked in the multi-open argument
    //
    // NB: Queries corresponding to simple, multiplicative selectors need not be
    // checked
    let queries = committed_instances
        .iter()
        .zip(instance_evals.iter())
        .zip(advice_commitments.iter())
        .zip(advice_evals.iter())
        .zip(permutations_evaluated.iter())
        .zip(lookups_evaluated.iter())
        .zip(trashcans_evaluated.iter())
        .flat_map(
            |(
                (
                    (
                        (((committed_instances, instance_evals), advice_commitments), advice_evals),
                        permutation,
                    ),
                    lookups,
                ),
                trash,
            )| {
                iter::empty()
                    .chain(vk.cs.advice_queries.iter().enumerate().map(
                        move |(query_index, &(column, at))| {
                            VerifierQuery::new(
                                vk.domain.rotate_omega(x, at),
                                CommitmentLabel::Advice(column.index()),
                                &advice_commitments[column.index()],
                                advice_evals[query_index],
                            )
                        },
                    ))
                    .chain(vk.cs.instance_queries.iter().enumerate().filter_map(
                        move |(query_index, &(column, at))| {
                            if column.index() < nb_committed_instances {
                                Some(VerifierQuery::new(
                                    vk.domain.rotate_omega(x, at),
                                    CommitmentLabel::Instance(column.index()),
                                    &committed_instances[column.index()],
                                    instance_evals[query_index],
                                ))
                            } else {
                                None
                            }
                        },
                    ))
                    .chain(permutation.queries(vk, x))
                    .chain(lookups.iter().flat_map(move |p| p.queries(vk, x)))
                    .chain(trash.iter().flat_map(move |p| p.queries(x)))
            },
        )
        .chain(
            vk.cs
                .fixed_queries
                .iter()
                .enumerate()
                // Filter out queries for simple, multiplicative selectors
                .filter(|(_, (col, _))| !vk.cs.has_simple_selector_col(col.index()))
                .map(|(query_index, &(column, at))| {
                    VerifierQuery::new(
                        vk.domain.rotate_omega(x, at),
                        CommitmentLabel::Fixed(column.index()),
                        &vk.fixed_commitments[column.index()],
                        fixed_evals[query_index],
                    )
                }),
        )
        .chain(permutations_common.queries(&vk.permutation, x))
        .chain(iter::once(lin_com))
        .collect::<Vec<_>>();

    // We are now convinced the circuit is satisfied so long as the
    // polynomial commitments open to the correct values.
    CS::multi_prepare(&queries, transcript).map_err(|_| Error::Opening)
}

/// Prepares a plonk proof into a PCS instance that can be finalized or
/// batched. It is responsibility of the verifier to check the validity of the
/// instance columns.
///
/// The verifier will error if there are trailing bytes in the transcript.
pub fn prepare<F, CS: PolynomialCommitmentScheme<F>, T: Transcript>(
    vk: &VerifyingKey<F, CS>,
    // Unlike the prover, the verifier gets their instances in two arguments:
    // committed and normal (non-committed). Note that the total number of
    // instance columns is expected to be the sum of committed instances and
    // normal instances for every proof. (Committed instances go first, that is,
    // the first instance columns are devoted to committed instances.)
    #[cfg(feature = "committed-instances")] committed_instances: &[&[CS::Commitment]],
    instances: &[&[&[F]]],
    transcript: &mut T,
) -> Result<CS::VerificationGuard, Error>
where
    F: WithSmallOrderMulGroup<3>
        + Hashable<T::Hash>
        + Sampleable<T::Hash>
        + FromUniformBytes<64>
        + Hash
        + Ord,
    CS::Commitment: Hashable<T::Hash>,
    <T::Hash as crate::transcript::TranscriptHash>::Input: TranscriptInputBytes,
{
    let trace = parse_trace(
        vk,
        #[cfg(feature = "committed-instances")]
        committed_instances,
        instances,
        transcript,
    )?;

    verify_algebraic_constraints(
        vk,
        trace,
        #[cfg(feature = "committed-instances")]
        committed_instances,
        instances,
        transcript,
    )
}
