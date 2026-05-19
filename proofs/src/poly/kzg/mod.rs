//! We implement the multi-open technique developed in Halo 2. It is designed to
//! efficiently open multiple polynomials at multiple points while minimizing
//! proof size and verification time. In a nutshell, multiple opening queries
//! are batched into a single query by combining the target
//! polynomials/commitments and evaluation points using verifier-chosen
//! random scalars.
//!
//! For a more detailed explanation, see the [Halo 2 Book](https://zcash.github.io/halo2/design/proving-system/multipoint-opening.html) on Multipoint Openings.

use std::marker::PhantomData;

use midnight_curves::pairing::Engine;

#[cfg(feature = "fewer-point-sets")]
use super::query::Query;

/// Multiscalar multiplication engines
pub mod msm;
/// KZG commitment scheme
pub mod params;
mod utils;

use std::{fmt::Debug, hash::Hash};

use ff::Field;
use group::Group;
use midnight_curves::pairing::MultiMillerLoop;
use rand_core::OsRng;
pub use utils::compute_dummy_queries;

#[cfg(feature = "fewer-point-sets")]
mod fewer_point_sets_runtime {
    use std::cell::Cell;

    thread_local! {
        static ENABLED: Cell<bool> = const { Cell::new(true) };
    }

    pub fn enabled() -> bool {
        ENABLED.with(Cell::get)
    }

    /// Guard that restores the previous fewer-point-sets runtime setting when
    /// dropped.
    #[derive(Debug)]
    pub struct ScopedFewerPointSets {
        previous: bool,
    }

    pub fn scoped(enabled: bool) -> ScopedFewerPointSets {
        let previous = ENABLED.with(|cell| {
            let previous = cell.get();
            cell.set(enabled);
            previous
        });
        ScopedFewerPointSets { previous }
    }

    impl Drop for ScopedFewerPointSets {
        fn drop(&mut self) {
            ENABLED.with(|cell| cell.set(self.previous));
        }
    }
}

#[cfg(feature = "fewer-point-sets")]
pub use fewer_point_sets_runtime::ScopedFewerPointSets;

/// No-op guard returned when the proof-system fewer-point-sets capability is
/// not compiled in.
#[cfg(not(feature = "fewer-point-sets"))]
#[derive(Debug)]
pub struct ScopedFewerPointSets;

/// Returns whether KZG multi-open dummy queries are currently enabled.
///
/// With the `fewer-point-sets` feature compiled in, the default is `true` to
/// preserve the historical feature behavior. Call [`scoped_fewer_point_sets`]
/// to temporarily override it for a specific proof.
pub fn fewer_point_sets_enabled() -> bool {
    #[cfg(feature = "fewer-point-sets")]
    {
        fewer_point_sets_runtime::enabled()
    }
    #[cfg(not(feature = "fewer-point-sets"))]
    {
        false
    }
}

/// Temporarily enables or disables KZG multi-open dummy queries on this thread.
///
/// This is intentionally scoped so recursive proving can use fewer point sets
/// for proofs verified inside a circuit while an outer proof in the same
/// process can be emitted without dummy query scalars.
pub fn scoped_fewer_point_sets(enabled: bool) -> ScopedFewerPointSets {
    #[cfg(feature = "fewer-point-sets")]
    {
        fewer_point_sets_runtime::scoped(enabled)
    }
    #[cfg(not(feature = "fewer-point-sets"))]
    {
        let _ = enabled;
        ScopedFewerPointSets
    }
}

#[cfg(feature = "solidity-verifier-trace")]
use crate::transcript::TranscriptInputBytes;
#[cfg(feature = "truncated-challenges")]
use crate::utils::arithmetic::{truncate, truncated_powers};
use crate::{
    poly::{
        commitment::PolynomialCommitmentScheme,
        kzg::{
            msm::{msm_specific, DualMSM, MSMKZG},
            params::{ParamsKZG, ParamsVerifierKZG},
            utils::construct_intermediate_sets,
        },
        query::{CommitmentLabel, CommitmentReference, VerifierQuery},
        Coeff, Error, LagrangeCoeff, Polynomial, ProverQuery,
    },
    transcript::{Hashable, Sampleable, Transcript},
    utils::{
        arithmetic::{
            eval_polynomial, evals_inner_product, inner_product, kate_division,
            lagrange_interpolate, msm_inner_product, powers, CurveAffine, CurveExt, MSM,
        },
        helpers::ProcessedSerdeObject,
    },
};

#[cfg(feature = "truncated-challenges")]
mod truncated_challenges_runtime {
    use std::cell::Cell;

    thread_local! {
        static ENABLED: Cell<bool> = const { Cell::new(true) };
    }

    pub fn enabled() -> bool {
        ENABLED.with(Cell::get)
    }

    /// Guard that restores the previous truncated-challenges setting when
    /// dropped.
    #[derive(Debug)]
    pub struct ScopedTruncatedChallenges {
        previous: bool,
    }

    pub fn scoped(enabled: bool) -> ScopedTruncatedChallenges {
        let previous = ENABLED.with(|cell| {
            let previous = cell.get();
            cell.set(enabled);
            previous
        });
        ScopedTruncatedChallenges { previous }
    }

    impl Drop for ScopedTruncatedChallenges {
        fn drop(&mut self) {
            ENABLED.with(|cell| cell.set(self.previous));
        }
    }
}

#[cfg(feature = "truncated-challenges")]
pub use truncated_challenges_runtime::ScopedTruncatedChallenges;

/// No-op guard returned when the proof-system truncated-challenges capability
/// is not compiled in.
#[cfg(not(feature = "truncated-challenges"))]
#[derive(Debug)]
pub struct ScopedTruncatedChallenges;

/// Returns whether KZG PCS challenge truncation is currently enabled.
///
/// With the `truncated-challenges` feature compiled in, the default is `true`
/// to preserve the historical feature behavior. Call
/// [`scoped_truncated_challenges`] to temporarily override it for a specific
/// outer proof.
pub fn truncated_challenges_enabled() -> bool {
    #[cfg(feature = "truncated-challenges")]
    {
        truncated_challenges_runtime::enabled()
    }
    #[cfg(not(feature = "truncated-challenges"))]
    {
        false
    }
}

/// Temporarily enables or disables KZG PCS challenge truncation on this thread.
///
/// This is intentionally scoped so recursive proving can keep truncated
/// challenges for proofs verified inside a circuit while a final
/// Solidity-facing proof in the same process can be emitted with full-width PCS
/// challenges.
pub fn scoped_truncated_challenges(enabled: bool) -> ScopedTruncatedChallenges {
    #[cfg(feature = "truncated-challenges")]
    {
        truncated_challenges_runtime::scoped(enabled)
    }
    #[cfg(not(feature = "truncated-challenges"))]
    {
        let _ = enabled;
        ScopedTruncatedChallenges
    }
}

fn pcs_challenge<F: ff::PrimeField>(challenge: F) -> F {
    #[cfg(feature = "truncated-challenges")]
    {
        if truncated_challenges_enabled() {
            return truncate(challenge);
        }
    }
    challenge
}

fn pcs_powers<F: ff::PrimeField>(base: F, len: usize) -> Vec<F> {
    #[cfg(feature = "truncated-challenges")]
    {
        if truncated_challenges_enabled() {
            return truncated_powers(base).take(len).collect();
        }
    }

    let mut acc = F::ONE;
    let mut out = Vec::with_capacity(len);
    for _ in 0..len {
        out.push(pcs_challenge(acc));
        acc *= base;
    }
    out
}

#[derive(Clone, Debug)]
/// KZG verifier
pub struct KZGCommitmentScheme<E: Engine> {
    _marker: PhantomData<E>,
}

impl<E: MultiMillerLoop> PolynomialCommitmentScheme<E::Fr> for KZGCommitmentScheme<E>
where
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    type Parameters = ParamsKZG<E>;
    type VerifierParameters = ParamsVerifierKZG<E>;
    type Commitment = E::G1;
    type VerificationGuard = DualMSM<E>;

    fn gen_params(k: u32) -> Self::Parameters {
        ParamsKZG::unsafe_setup(k, OsRng)
    }

    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters {
        params.verifier_params()
    }

    fn commit(
        params: &Self::Parameters,
        polynomial: &Polynomial<E::Fr, Coeff>,
    ) -> Self::Commitment {
        let size = polynomial.values.len();
        assert!(params.g.len() >= size);
        msm_specific::<E::G1Affine>(&polynomial.values, &params.g[..size])
    }

    fn commit_lagrange(
        params: &Self::Parameters,
        poly: &Polynomial<E::Fr, LagrangeCoeff>,
    ) -> E::G1 {
        let size = poly.values.len();

        assert!(params.g_lagrange.len() >= size);

        msm_specific::<E::G1Affine>(&poly.values, &params.g_lagrange[0..size])
    }

    fn multi_open<T: Transcript>(
        params: &Self::Parameters,
        queries: &[ProverQuery<E::Fr>],
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        E::Fr: Sampleable<T::Hash> + Hash + Ord + Hashable<T::Hash>,
        E::G1: Hashable<T::Hash>,
    {
        /// Like [`inner_product`] but for coefficient-form polynomials that may
        /// have different lengths (zero-extending the shorter operands via
        /// [`Polynomial::padded_add`]).
        fn poly_inner_product<F: ff::PrimeField>(
            polys: &[Polynomial<F, Coeff>],
            scalars: impl Iterator<Item = F>,
        ) -> Polynomial<F, Coeff> {
            polys
                .iter()
                .zip(scalars)
                .map(|(p, s)| p.clone() * s)
                .reduce(|acc, p| acc.padded_add(&p))
                .unwrap()
        }

        #[cfg(feature = "fewer-point-sets")]
        let queries_with_dummies;
        #[cfg(feature = "fewer-point-sets")]
        let queries = if fewer_point_sets_enabled() {
            // Add dummy queries to reduce the number of distinct multi-open point sets.
            queries_with_dummies = {
                let mut queries = queries.to_vec();
                let pairs: Vec<_> = queries.iter().map(|q| (q.get_commitment(), q.point)).collect();
                for (idx, point) in compute_dummy_queries(&pairs) {
                    let poly = queries[idx].poly;
                    transcript
                        .write(&eval_polynomial(poly, point))
                        .map_err(|_| Error::OpeningError)?;
                    queries.push(ProverQuery::new(point, poly));
                }
                queries
            };
            &queries_with_dummies
        } else {
            queries
        };

        // Refer to the halo2 book for docs:
        // https://zcash.github.io/halo2/design/proving-system/multipoint-opening.html
        let x1: E::Fr = transcript.squeeze_challenge();
        let x2: E::Fr = transcript.squeeze_challenge();

        let (poly_map, point_sets) = construct_intermediate_sets(queries)?;

        let mut q_polys = vec![vec![]; point_sets.len()];

        for com_data in poly_map.iter() {
            q_polys[com_data.set_index].push(com_data.commitment.poly.clone());
        }

        let q_polys = q_polys
            .iter()
            .map(|polys| poly_inner_product(polys, pcs_powers(x1, polys.len()).into_iter()))
            .collect::<Vec<_>>();

        // Sort point sets by ascending cardinality to ensure the first set is the one
        // that contains fixed commitments (which are evaluated at x only). This
        // property is not necessary for the actual proving system, but it is important
        // for in-circuit verification of proofs. (It enables an optimization based on
        // an internal collapse.)
        //
        // The (len, i) key provides a deterministic total order even when two sets
        // share the same cardinality.
        let (q_polys, point_sets) = {
            let mut order: Vec<usize> = (0..point_sets.len()).collect();
            order.sort_by_key(|&i| (point_sets[i].len(), i));
            let q_polys: Vec<_> = order.iter().map(|&i| q_polys[i].clone()).collect();
            let point_sets: Vec<_> = order.iter().map(|&i| point_sets[i].clone()).collect();
            (q_polys, point_sets)
        };

        let f_poly = {
            let f_polys = point_sets
                .iter()
                .zip(q_polys.clone())
                .map(|(points, q_poly)| {
                    let poly = points.iter().fold(q_poly.clone().values, |poly, point| {
                        kate_division(&poly, *point)
                    });
                    Polynomial {
                        values: poly,
                        _marker: PhantomData,
                    }
                })
                .collect::<Vec<_>>();
            poly_inner_product(&f_polys, powers(x2))
        };

        let f_com = Self::commit(params, &f_poly);
        transcript.write(&f_com).map_err(|_| Error::OpeningError)?;

        let x3: E::Fr = transcript.squeeze_challenge();
        let x3 = pcs_challenge(x3);

        for q_poly in q_polys.iter() {
            transcript
                .write(&eval_polynomial(&q_poly.values, x3))
                .map_err(|_| Error::OpeningError)?;
        }

        let x4: E::Fr = transcript.squeeze_challenge();

        let final_poly = {
            let mut polys = q_polys;
            polys.push(f_poly);
            poly_inner_product(&polys, pcs_powers(x4, polys.len()).into_iter())
        };
        let v = eval_polynomial(&final_poly, x3);

        let pi = {
            let pi_poly = Polynomial {
                values: kate_division(&(&final_poly - v).values, x3),
                _marker: PhantomData,
            };
            Self::commit(params, &pi_poly)
        };

        transcript.write(&pi).map_err(|_| Error::OpeningError)
    }

    fn multi_prepare<'com, T: Transcript>(
        queries: &[VerifierQuery<'com, E::Fr, KZGCommitmentScheme<E>>],
        transcript: &mut T,
    ) -> Result<DualMSM<E>, Error>
    where
        E::Fr: Sampleable<T::Hash> + Ord + Hash + Hashable<T::Hash>,
        E::G1: 'com + Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr>,
        <T::Hash as crate::transcript::TranscriptHash>::Input:
            crate::transcript::TranscriptInputBytes,
    {
        #[cfg(feature = "fewer-point-sets")]
        let queries_with_dummies;
        #[cfg(feature = "fewer-point-sets")]
        let queries = if fewer_point_sets_enabled() {
            // Add dummy queries to reduce the number of distinct multi-open point sets.
            queries_with_dummies = {
                let mut queries = queries.to_vec();
                let pairs: Vec<_> =
                    queries.iter().map(|q| (q.commitment.clone(), q.point)).collect();
                for (idx, point) in compute_dummy_queries(&pairs) {
                    let eval = transcript.read().map_err(|_| Error::SamplingError)?;
                    #[cfg(feature = "solidity-verifier-trace")]
                    crate::plonk::solidity_trace::record_proof_eval::<T::Hash, _>(
                        "proof_dummy_eval",
                        &eval,
                    );
                    queries.push(VerifierQuery {
                        point,
                        commitment_label: queries[idx].commitment_label.clone(),
                        commitment: queries[idx].commitment.clone(),
                        eval,
                    });
                }
                queries
            };
            &queries_with_dummies
        } else {
            queries
        };

        // Refer to the halo2 book for docs:
        // https://zcash.github.io/halo2/design/proving-system/multipoint-opening.html
        let x1: E::Fr = transcript.squeeze_challenge();
        let x2: E::Fr = transcript.squeeze_challenge();
        #[cfg(feature = "solidity-verifier-trace")]
        {
            crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(13, "x1", &x1);
            crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(14, "x2", &x2);
        }

        let (commitment_map, point_sets) = construct_intermediate_sets(queries)?;

        let mut q_coms: Vec<_> = vec![vec![]; point_sets.len()];
        let mut q_eval_sets = vec![vec![]; point_sets.len()];

        for com_data in commitment_map.into_iter() {
            let mut msm = MSMKZG::init();
            let terms = com_data.commitment.as_terms();
            let term_labels: Vec<CommitmentLabel> = match &com_data.commitment {
                CommitmentReference::Linear(_, _, labels) => labels.clone(),
                _ => vec![com_data.commitment_label.clone(); terms.len()],
            };
            for ((scalar, commitment), label) in terms.into_iter().zip(term_labels) {
                msm.append_term(scalar, commitment, label);
            }
            q_coms[com_data.set_index].push(msm);
            q_eval_sets[com_data.set_index].push(com_data.evals);
        }

        let nb_x1_powers = q_coms.iter().map(|v| v.len()).max().unwrap_or(0);
        assert!(nb_x1_powers >= q_eval_sets.iter().map(|v| v.len()).max().unwrap_or(0));

        let powers_x1 = pcs_powers(x1, nb_x1_powers);

        let q_coms = q_coms
            .into_iter()
            .map(|msms| msm_inner_product(msms, &powers_x1))
            .collect::<Vec<_>>();

        let q_eval_sets = q_eval_sets
            .iter()
            .map(|evals| evals_inner_product(evals, &powers_x1))
            .collect::<Vec<_>>();

        // Sort point sets by ascending cardinality to ensure the first set is the one
        // that contains fixed commitments (which are evaluated at x only). This
        // property is not necessary for the actual proving system, but it is important
        // for in-circuit verification of proofs. (It enables an optimization based on
        // an internal collapse.)
        //
        // The (len, i) key provides a deterministic total order even when two sets
        // share the same cardinality.
        let (q_coms, q_eval_sets, point_sets) = {
            let mut order: Vec<usize> = (0..point_sets.len()).collect();
            order.sort_by_key(|&i| (point_sets[i].len(), i));
            let q_coms: Vec<_> = order.iter().map(|&i| q_coms[i].clone()).collect();
            let q_eval_sets: Vec<_> = order.iter().map(|&i| q_eval_sets[i].clone()).collect();
            let point_sets: Vec<_> = order.iter().map(|&i| point_sets[i].clone()).collect();
            (q_coms, q_eval_sets, point_sets)
        };
        #[cfg(feature = "solidity-verifier-trace")]
        {
            for (idx, points) in point_sets.iter().enumerate() {
                let mut data = Vec::with_capacity(points.len() * 32);
                for point in points {
                    data.extend_from_slice(&point.to_input().into_trace_bytes());
                }
                crate::plonk::solidity_trace::record_bytes(
                    crate::plonk::solidity_trace::PCS_POINT_SET_TRACE_BASE + idx as u64,
                    "pcs_point_set",
                    data,
                );
            }
            for (idx, q_com) in q_coms.iter().enumerate() {
                crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
                    crate::plonk::solidity_trace::PCS_Q_COM_TRACE_BASE + idx as u64,
                    "pcs_q_com",
                    &q_com.eval(),
                );
            }
        }

        let f_com: E::G1 = transcript.read().map_err(|_| Error::SamplingError)?;
        #[cfg(feature = "solidity-verifier-trace")]
        crate::plonk::solidity_trace::record_proof_commitment::<T::Hash, _>("proof_f_com", &f_com);
        #[cfg(feature = "solidity-verifier-trace")]
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(25, "f_com", &f_com);

        // Sample a challenge x_3 for checking that f(X) was committed to
        // correctly.
        let x3: E::Fr = transcript.squeeze_challenge();
        let x3 = pcs_challenge(x3);
        #[cfg(feature = "solidity-verifier-trace")]
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(15, "x3", &x3);

        let mut q_evals_on_x3 = Vec::<E::Fr>::with_capacity(q_eval_sets.len());
        for _ in 0..q_eval_sets.len() {
            let eval = transcript.read().map_err(|_| Error::SamplingError)?;
            #[cfg(feature = "solidity-verifier-trace")]
            crate::plonk::solidity_trace::record_proof_eval::<T::Hash, _>("proof_q_eval", &eval);
            q_evals_on_x3.push(eval);
        }

        // We can compute the expected msm_eval at x_3 using the u provided
        // by the prover and from x_2
        let f_eval =
            point_sets.iter().zip(q_eval_sets.iter()).zip(q_evals_on_x3.iter()).rev().fold(
                E::Fr::ZERO,
                |acc_eval, ((points, evals), proof_eval)| {
                    let r_poly = lagrange_interpolate(points, evals);
                    let r_eval = eval_polynomial(&r_poly, x3);
                    // eval = (proof_eval - r_eval) / prod_i (x3 - point_i)
                    let den = points.iter().fold(E::Fr::ONE, |acc, point| acc * &(x3 - point));
                    let eval = (*proof_eval - &r_eval) * den.invert().unwrap();
                    acc_eval * &(x2) + &eval
                },
            );

        let x4: E::Fr = transcript.squeeze_challenge();
        #[cfg(feature = "solidity-verifier-trace")]
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(16, "x4", &x4);

        let final_com = {
            let size = q_coms.len() + 1;
            let mut coms = q_coms;
            let mut f_com_as_msm = MSMKZG::init();

            f_com_as_msm.append_term(E::Fr::ONE, f_com, CommitmentLabel::NoLabel);

            // Collapse all MSMs before combining with truncated x4 powers, to
            // match the in-circuit verifier. Skip the first one since its x4
            // power is 1.
            if truncated_challenges_enabled() {
                coms.iter_mut().skip(1).for_each(MSMKZG::collapse);
            }
            coms.push(f_com_as_msm);

            msm_inner_product(coms, &pcs_powers(x4, size))
        };
        #[cfg(feature = "solidity-verifier-trace")]
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
            33,
            "final_com",
            &final_com.eval(),
        );

        let v = {
            let mut evals = q_evals_on_x3;
            evals.push(f_eval);

            inner_product(&evals, pcs_powers(x4, evals.len()).into_iter())
        };
        #[cfg(feature = "solidity-verifier-trace")]
        {
            crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(31, "f_eval", &f_eval);
            crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(32, "v", &v);
        }

        let pi: E::G1 = transcript.read().map_err(|_| Error::SamplingError)?;
        #[cfg(feature = "solidity-verifier-trace")]
        crate::plonk::solidity_trace::record_proof_commitment::<T::Hash, _>("proof_pi", &pi);
        #[cfg(feature = "solidity-verifier-trace")]
        crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(26, "pi", &pi);

        let mut pi_msm = MSMKZG::<E>::init();
        pi_msm.append_term(E::Fr::ONE, pi, CommitmentLabel::Custom("π".into()));

        // Scale zπ - vG
        let scaled_pi = MSMKZG {
            scalars: vec![x3, v],
            bases: vec![pi, -E::G1::generator()],
            labels: vec![
                CommitmentLabel::Custom("π".into()),
                CommitmentLabel::Custom("-G".into()),
            ],
        };

        // (π, C − vG + zπ)
        let mut msm_accumulator = DualMSM {
            left: pi_msm,
            right: final_com,
        };
        msm_accumulator.right.add_msm(&scaled_pi);
        #[cfg(feature = "solidity-verifier-trace")]
        {
            crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
                27,
                "pairing_lhs",
                &msm_accumulator.left.eval(),
            );
            crate::plonk::solidity_trace::record_hashable::<T::Hash, _>(
                28,
                "pairing_rhs",
                &msm_accumulator.right.eval(),
            );
        }

        Ok(msm_accumulator)
    }
}

#[cfg(test)]
mod tests {
    use std::hash::Hash;

    use blake2b_simd::State as Blake2bState;
    use ff::WithSmallOrderMulGroup;
    use midnight_curves::{pairing::MultiMillerLoop, serde::SerdeObject, CurveAffine, CurveExt};
    use rand_core::OsRng;

    use crate::{
        poly::{
            commitment::{Guard, PolynomialCommitmentScheme},
            kzg::{
                params::{ParamsKZG, ParamsVerifierKZG},
                KZGCommitmentScheme,
            },
            query::{ProverQuery, VerifierQuery},
            CommitmentLabel, EvaluationDomain,
        },
        transcript::{
            CircuitTranscript, Hashable, Sampleable, Transcript, TranscriptHash,
            TranscriptInputBytes,
        },
        utils::arithmetic::eval_polynomial,
    };

    #[cfg(feature = "truncated-challenges")]
    #[test]
    fn scoped_truncated_challenges_overrides_pcs_challenge() {
        use ff::Field;
        use midnight_curves::Fq;

        let high_bit = Fq::from(2).pow_vartime([200, 0, 0, 0]);

        assert_eq!(super::pcs_challenge(high_bit), Fq::ZERO);
        {
            let _guard = super::scoped_truncated_challenges(false);
            assert_eq!(super::pcs_challenge(high_bit), high_bit);
        }
        assert_eq!(super::pcs_challenge(high_bit), Fq::ZERO);
    }

    #[test]
    fn test_roundtrip_gwc() {
        use midnight_curves::Bls12;

        const K: u32 = 4;

        let params: ParamsKZG<Bls12> = ParamsKZG::unsafe_setup(K, OsRng);

        let proof = create_proof::<_, CircuitTranscript<Blake2bState>>(&params);

        let verifier_params = params.verifier_params();
        verify::<Bls12, CircuitTranscript<Blake2bState>>(&verifier_params, &proof[..], false);

        verify::<Bls12, CircuitTranscript<Blake2bState>>(&verifier_params, &proof[..], true);
    }

    fn verify<E, T>(verifier_params: &ParamsVerifierKZG<E>, proof: &[u8], should_fail: bool)
    where
        E: MultiMillerLoop,
        T: Transcript,
        E::Fr: Hashable<T::Hash> + Sampleable<T::Hash> + Ord + Hash,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
        E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
        <T::Hash as TranscriptHash>::Input: TranscriptInputBytes,
    {
        let mut transcript = T::init_from_bytes(proof);

        let a: E::G1 = transcript.read().unwrap();
        let b: E::G1 = transcript.read().unwrap();
        let c: E::G1 = transcript.read().unwrap();

        let x: E::Fr = transcript.squeeze_challenge();
        let y: E::Fr = transcript.squeeze_challenge();

        let avx: E::Fr = transcript.read().unwrap();
        let bvx: E::Fr = transcript.read().unwrap();
        let cvy: E::Fr = transcript.read().unwrap();

        use CommitmentLabel::NoLabel;
        let valid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new(x, NoLabel, &a, avx)))
            .chain(Some(VerifierQuery::new(x, NoLabel, &b, bvx)))
            .chain(Some(VerifierQuery::new(y, NoLabel, &c, cvy)));

        let invalid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new(x, NoLabel, &a, avx)))
            .chain(Some(VerifierQuery::new(x, NoLabel, &b, avx)))
            .chain(Some(VerifierQuery::new(y, NoLabel, &c, cvy)));

        let queries = if should_fail {
            invalid_queries
        } else {
            valid_queries
        };

        let result =
            KZGCommitmentScheme::multi_prepare(&queries.collect::<Vec<_>>(), &mut transcript)
                .unwrap();

        if should_fail {
            assert!(result.verify(verifier_params).is_err());
        } else {
            assert!(result.verify(verifier_params).is_ok());
        }
    }

    fn create_proof<E, T>(kzg_params: &ParamsKZG<E>) -> Vec<u8>
    where
        E: MultiMillerLoop,
        T: Transcript,
        E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Hash + Sampleable<T::Hash> + Ord,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
        E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
        <T::Hash as TranscriptHash>::Input: TranscriptInputBytes,
    {
        let k = (kzg_params.g.len() - 1).ilog2() + 1;
        let domain = EvaluationDomain::new(1, k);

        let mut ax = domain.empty_coeff();
        for (i, a) in ax.iter_mut().enumerate() {
            *a = <E::Fr>::from(10 + i as u64);
        }

        let mut bx = domain.empty_coeff();
        for (i, a) in bx.iter_mut().enumerate() {
            *a = <E::Fr>::from(100 + i as u64);
        }

        let mut cx = domain.empty_coeff();
        for (i, a) in cx.iter_mut().enumerate() {
            *a = <E::Fr>::from(100 + i as u64);
        }

        let mut transcript = T::init();

        let a = KZGCommitmentScheme::commit(kzg_params, &ax);
        let b = KZGCommitmentScheme::commit(kzg_params, &bx);
        let c = KZGCommitmentScheme::commit(kzg_params, &cx);

        transcript.write(&a).unwrap();
        transcript.write(&b).unwrap();
        transcript.write(&c).unwrap();

        let x: E::Fr = transcript.squeeze_challenge();
        let y = transcript.squeeze_challenge();

        let avx = eval_polynomial(&ax, x);
        let bvx = eval_polynomial(&bx, x);
        let cvy = eval_polynomial(&cx, y);

        transcript.write(&avx).unwrap();
        transcript.write(&bvx).unwrap();
        transcript.write(&cvy).unwrap();

        let queries = [
            ProverQuery {
                point: x,
                poly: &ax,
            },
            ProverQuery {
                point: x,
                poly: &bx,
            },
            ProverQuery {
                point: y,
                poly: &cx,
            },
        ]
        .into_iter();

        KZGCommitmentScheme::multi_open(kzg_params, &queries.collect::<Vec<_>>(), &mut transcript)
            .unwrap();

        transcript.finalize()
    }
}
