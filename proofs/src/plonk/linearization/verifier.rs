use std::collections::BTreeMap;

use ff::PrimeField;

use crate::{
    plonk::VerifyingKey,
    poly::{commitment::PolynomialCommitmentScheme, CommitmentLabel, VerifierQuery},
};

/// Construct the commitment to the linearization polynomial
/// (which will be checked that it opens to `0` at `x` in the multi-open
/// argument):
///
///  `S_0 * id_0(x) + y * S_1 * id_1(x) + ... + y^m * S_m * id_m(x)
///        - (h_0 + x^{n-1} * h_1 + ... + x^{l*(n-1)} * h_l) * (x^n-1),`
///
/// where:
/// * `y` is the batching challenge,
/// * `x` is the evaluation challenge,
/// * `id_j(x)` is a (partially or fully) evaluated identity at `x`,
/// * `S_j` is, either,
///      - (i)  the commitment to a fixed column representing a simple,
///        multiplicative selector, or,
///      - (ii) the commitment to the constant polynomial `P(X) = 1` (in case
///        the corresponding identity `id_j` has been fully evaluated and, thus,
///        the resulting scalar is part of the constant term of the
///        linearization polynomial)
/// * `h_k` are commitments to the limbs of the quotient polynomial.
///
/// # Arguments
///
/// * `expressions` - the output of
///   [crate::plonk::partially_evaluate_identities]
/// * `splitting_factor` - the evaluated splitting factor `x^{n-1}` from
///   decomposing the quotient polynomial `h(T)` into limbs
///
/// # Returns
///
/// A [VerifierQuery], that checks if the commitment to the linearization
/// polynomial opens to `0` at the evaluation challenge `x`. The commitment
/// itself is an MSM represented as a vector of points and a vector
/// of scalars.
#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn compute_linearization_commitment<
    'com,
    F: PrimeField + ff::WithSmallOrderMulGroup<3> + ff::FromUniformBytes<64> + std::cmp::Ord,
    CS: PolynomialCommitmentScheme<F>,
>(
    expressions: Vec<(Option<usize>, F)>,
    vk: &'com VerifyingKey<F, CS>,
    x: F,
    y: &F,
    xn: &F,
    splitting_factor: &F,
    quotient_limb_commitments: &'com [CS::Commitment],
) -> VerifierQuery<'com, F, CS> {
    let lin_com_len = vk.cs.num_simple_selectors() + quotient_limb_commitments.len() + 1;
    let mut identities_points = Vec::with_capacity(lin_com_len);
    let mut identities_scalars = Vec::with_capacity(lin_com_len);
    let mut identities_labels = Vec::with_capacity(lin_com_len);

    identities_points.extend(quotient_limb_commitments);

    #[cfg(feature = "debug-trace-hooks")]
    if crate::debug_trace::is_enabled() {
        use crate::debug_trace::{emit_scalar, emit_usize};
        emit_scalar("linearization.y", y);
        emit_scalar("linearization.x", &x);
        emit_scalar("linearization.xn", xn);
        emit_scalar("linearization.splitting_factor", splitting_factor);
        emit_usize(
            "linearization.num_quotient_limbs",
            quotient_limb_commitments.len(),
        );
    }

    let mut splitting_pow = F::ONE - *xn;
    for _ in 0..quotient_limb_commitments.len() {
        identities_scalars.push(splitting_pow);
        identities_labels.push(CommitmentLabel::NoLabel);
        splitting_pow *= splitting_factor;
    }

    #[cfg(feature = "debug-trace-hooks")]
    if crate::debug_trace::is_enabled() {
        use crate::debug_trace::emit_scalar;
        // Emit the quotient-limb scalars (the pre-grouping part of the MSM).
        for (i, s) in identities_scalars.iter().enumerate() {
            emit_scalar(&format!("linearization.quotient_limb_scalar[{i}]"), s);
        }
    }

    // Group multiples of the same point in the MSM
    let mut grouped_points: BTreeMap<Option<usize>, F> = BTreeMap::new();
    let mut y_pow = F::ONE;
    expressions.iter().rev().for_each(|(col_idx, eval)| {
        *grouped_points.entry(*col_idx).or_insert(F::ZERO) += y_pow * eval;
        y_pow *= y;
    });

    let mut expected_eval = F::ZERO;
    grouped_points.into_iter().for_each(|(col_idx, eval)| {
        match col_idx {
            Some(col_idx) => {
                identities_points.push(&vk.fixed_commitments[col_idx]);
                identities_labels.push(CommitmentLabel::Fixed(col_idx));
                identities_scalars.push(eval);
            }
            // Fully evaluated identities are not included and pass (negated)
            // to the evaluation side.
            None => {
                expected_eval -= eval;
            }
        }
    });

    #[cfg(feature = "debug-trace-hooks")]
    if crate::debug_trace::is_enabled() {
        use crate::debug_trace::{emit_bytes, emit_scalar, emit_u64, emit_usize};
        use group::GroupEncoding;
        emit_usize(
            "linearization.num_identities_after_group",
            identities_points.len(),
        );
        // Emit all grouped identity scalars (includes quotient-limb
        // prefix emitted above; duplicate payload is intentional so
        // consumers don't need to splice two slices together).
        for (i, s) in identities_scalars.iter().enumerate() {
            emit_scalar(&format!("linearization.identity_scalar[{i}]"), s);
        }
        // Emit per-identity label classification as a small u64 code.
        for (i, lbl) in identities_labels.iter().enumerate() {
            let code: u64 = match lbl {
                CommitmentLabel::NoLabel => 0,
                CommitmentLabel::Fixed(idx) => 0x1_0000_0000u64 | (*idx as u64),
                CommitmentLabel::Advice(idx) => 0x2_0000_0000u64 | (*idx as u64),
                CommitmentLabel::Instance(idx) => 0x3_0000_0000u64 | (*idx as u64),
                CommitmentLabel::Permutation(idx) => 0x4_0000_0000u64 | (*idx as u64),
                CommitmentLabel::Custom(_) => 0x5_0000_0000u64,
            };
            emit_u64(&format!("linearization.identity_label[{i}]"), code);
        }
        emit_scalar("linearization.expected_eval", &expected_eval);
        // Emit each linearization MSM point's GroupEncoding (compressed).
        // The Solidity `_linearizationSignature` folds point coords
        // (Fp halves in EIP-2537 encoding) into the signature; the
        // Rust-side cross-check test decompresses these bytes and
        // reconstructs the same halves.
        for (i, p) in identities_points.iter().enumerate() {
            let bytes = p.to_bytes();
            emit_bytes(
                &format!("linearization.point_compressed[{i}]"),
                bytes.as_ref(),
            );
        }
    }

    VerifierQuery::new_linear(
        x,
        CommitmentLabel::Custom("linearization_poly".into()),
        identities_points,
        identities_scalars,
        identities_labels,
        expected_eval,
    )
}
