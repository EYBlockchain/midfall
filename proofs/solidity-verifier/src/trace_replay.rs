//! Generic Fiat-Shamir replay helper used by the cross-trace tests
//! (poseidon, IVC).
//!
//! Given a midnight-proofs `VerifyingKey` and a Keccak256-transcript
//! proof produced for it, this walks the transcript exactly the way
//! `midnight-proofs::plonk::verify` would — common-input the VK
//! digest, common-input the committed instance commitment(s) and the
//! non-committed instance, then loop through phases / lookups /
//! permutation / trashcans / quotient limbs, then read all
//! evaluations, and finally drive the KZG multi-open transcript
//! sequence (`x1`, `x2`, `f_com`, `x3`, `q_evals`, `x4`, `pi`) — and
//! records every challenge / scalar read / point read into a
//! [`Trace`].
//!
//! The function is **CS-driven**, not circuit-specific: it walks the
//! `ConstraintSystem` exposed by the VK so the same code handles
//! `numLookups == 1` (poseidon, RSA) and `numLookups == 2` (IVC) and
//! any future circuit shape that fits the §7.2 invariants in
//! `ARCHITECTURE.md`.
//!
//! Used by:
//!
//! * `tests/forge.rs::rust_and_solidity_traces_match` — poseidon end-to-end
//!   transcript-level equivalence.
//! * `tests/ivc.rs::rust_and_solidity_ivc_traces_match` — IVC
//!   final-step Keccak256 transcript-level equivalence.

use ff::PrimeField;
use group::Group;
use midnight_curves::{Bls12, Fq, G1Projective};
#[cfg(feature = "fewer-point-sets")]
use midnight_proofs::poly::Rotation;
use midnight_proofs::{plonk::VerifyingKey, poly::kzg::KZGCommitmentScheme};

use crate::{eip2537, trace::Trace, transcript::TracingTranscript};

/// Replay the verifier's Keccak256 Fiat-Shamir sequence and record
/// every transcript-observable event in a [`Trace`].
///
/// `nb_committed_instances` is the number of committed-instance
/// commitments the prover absorbed before the non-committed instance
/// columns.
pub fn replay_trace_from_vk(
    vk: &VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
    proof: &[u8],
    public_inputs: &[Fq],
    nb_committed_instances: usize,
) -> Trace {
    let cs = vk.cs();
    let mut t = TracingTranscript::init_from_bytes(proof);

    // --- hash VK digest into transcript ----------------------------------
    t.common_fq(&vk.transcript_repr()).unwrap();
    t.trace
        .borrow_mut()
        .intermediate("vk_repr", eip2537::fq_to_be_hex(&vk.transcript_repr()));

    // --- hash committed instance commitments (G1::identity() in tree) ---
    let committed_identity: G1Projective = <G1Projective as Group>::identity();
    for _ in 0..nb_committed_instances {
        t.common_g1(&committed_identity).unwrap();
    }

    // --- hash non-committed instances -----------------------------------
    let normal_instance_columns = cs.num_instance_columns() - nb_committed_instances;
    for column in 0..normal_instance_columns {
        let values = if normal_instance_columns == 1 || column + 1 == normal_instance_columns {
            public_inputs
        } else {
            &[]
        };
        let inst_len = Fq::from_u128(values.len() as u128);
        t.common_fq(&inst_len).unwrap();
        for v in values {
            t.common_fq(v).unwrap();
        }
    }

    // --- phases: read advice + squeeze advice challenges ----------------
    for (phase_idx, _phase) in cs.phases().enumerate() {
        for i in 0..cs.num_advice_columns() {
            let _ = t
                .read_g1(&format!("advice[{i}]"))
                .unwrap_or_else(|e| panic!("read advice[{i}] phase {phase_idx}: {e}"));
        }
        for _ in 0..cs.num_challenges() {
            let _ = t.squeeze_fq("advice_challenge");
        }
    }
    let _theta = t.squeeze_fq("theta");

    // --- lookup multiplicities ------------------------------------------
    for _ in 0..cs.lookups().len() {
        let _ = t.read_g1("lookup_mult").unwrap();
    }

    let _beta = t.squeeze_fq("beta");
    let _gamma = t.squeeze_fq("gamma");

    // --- permutation products (one G1 per chunk) -------------------------
    let perm_chunks = {
        let chunk_len = cs.degree() - 2;
        let cols = cs.permutation().get_columns().len();
        if cols == 0 {
            0
        } else {
            cols.div_ceil(chunk_len)
        }
    };
    for _ in 0..perm_chunks {
        let _ = t.read_g1("perm_product").unwrap();
    }

    // --- lookup commitments: per lookup, helpers (nChunks) + accumulator
    for l in cs.lookups().iter() {
        let nc = l.chunk_by_degree(cs.degree()).num_chunks();
        for _ in 0..nc {
            let _ = t.read_g1("lookup_helper").unwrap();
        }
        let _ = t.read_g1("lookup_acc").unwrap();
    }

    let _trash_ch = t.squeeze_fq("trash_challenge");
    for _ in 0..cs.trashcans().len() {
        let _ = t.read_g1("trashcan").unwrap();
    }
    let _y = t.squeeze_fq("y");

    // --- quotient limbs ---------------------------------------------------
    let nb_q = vk.get_domain().get_quotient_poly_degree();
    for _ in 0..nb_q {
        let _ = t.read_g1("quotient_limb").unwrap();
    }

    let _x = t.squeeze_fq("x");

    // --- read all evaluation scalars in Rust iterator order --------------
    let num_fixed_q = cs
        .fixed_queries()
        .iter()
        .filter(|(c, _)| !cs.has_simple_selector_col(c.index()))
        .count();
    // For committed-instance columns the verifier *reads* the eval
    // from the transcript; for non-committed columns it computes the
    // eval locally via Lagrange interpolation, so no transcript read
    // is performed there.  `nb_committed_instances` is the column
    // index cutoff: instance queries on columns `< nb` are
    // transcript reads.
    let num_committed_instance_reads = cs
        .instance_queries()
        .iter()
        .filter(|(col, _)| col.index() < nb_committed_instances)
        .count();
    for _ in 0..num_committed_instance_reads {
        let _ = t.read_fq("committed_instance_eval").unwrap();
    }

    for i in 0..cs.advice_queries().len() {
        let _ = t.read_fq(&format!("advice_eval[{i}]")).unwrap();
    }
    for i in 0..num_fixed_q {
        let _ = t.read_fq(&format!("fixed_eval[{i}]")).unwrap();
    }
    for i in 0..cs.permutation().get_columns().len() {
        let _ = t.read_fq(&format!("perm_common[{i}]")).unwrap();
    }
    for i in 0..perm_chunks {
        let _ = t.read_fq("perm_cur").unwrap();
        let _ = t.read_fq("perm_next").unwrap();
        if i + 1 != perm_chunks {
            let _ = t.read_fq("perm_last").unwrap();
        }
    }
    for l in cs.lookups().iter() {
        let nc = l.chunk_by_degree(cs.degree()).num_chunks();
        let _ = t.read_fq("lookup_m_eval").unwrap();
        for _ in 0..nc {
            let _ = t.read_fq("lookup_helper_eval").unwrap();
        }
        let _ = t.read_fq("lookup_acc_eval").unwrap();
        let _ = t.read_fq("lookup_acc_next_eval").unwrap();
    }
    for _ in 0..cs.trashcans().len() {
        let _ = t.read_fq("trash_eval").unwrap();
    }

    // --- KZG multi-open --------------------------------------------------
    #[cfg(feature = "fewer-point-sets")]
    {
        let dummy_count = dummy_query_count(vk, _x, nb_committed_instances);
        for _ in 0..dummy_count {
            let _ = t.read_fq("dummy_eval").unwrap();
        }
    }
    let _x1 = t.squeeze_fq("x1");
    let _x2 = t.squeeze_fq("x2");
    let _f_com = t.read_g1("f_com").unwrap();
    let _x3 = t.squeeze_fq("x3");
    // Read remaining q_evals from the proof until only 48 bytes —
    // exactly one G1 point — remain.
    loop {
        let buf = t.inner_mut().buffer();
        let remaining = buf.get_ref().len() as i64 - buf.position() as i64;
        if remaining <= 48 {
            break;
        }
        let _ = t.read_fq("q_eval").unwrap();
    }
    let _x4 = t.squeeze_fq("x4");
    let _pi = t.read_g1("pi").unwrap();

    t.trace()
}

#[cfg(feature = "fewer-point-sets")]
fn dummy_query_count(
    vk: &VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
    x: Fq,
    nb_committed_instances: usize,
) -> usize {
    let cs = vk.cs();
    let domain = vk.get_domain();
    let chunk_len = cs.degree() - 2;
    let perm_chunks = {
        let cols = cs.permutation().get_columns().len();
        if cols == 0 {
            0
        } else {
            cols.div_ceil(chunk_len)
        }
    };
    let total_lookup_helpers: usize =
        cs.lookups().iter().map(|l| l.chunk_by_degree(cs.degree()).num_chunks()).sum();

    let advice_base = 0usize;
    let instance_base = advice_base + cs.num_advice_columns();
    let perm_prod_base = instance_base + cs.num_instance_columns();
    let lookup_m_base = perm_prod_base + perm_chunks;
    let lookup_helper_base = lookup_m_base + cs.lookups().len();
    let lookup_acc_base = lookup_helper_base + total_lookup_helpers;
    let trash_base = lookup_acc_base + cs.lookups().len();
    let fixed_base = trash_base + cs.trashcans().len();
    let perm_common_base = fixed_base + cs.num_fixed_columns();
    let lin_base = perm_common_base + cs.permutation().get_columns().len();

    let mut pairs = Vec::<(usize, Fq)>::new();
    for &(column, at) in cs.advice_queries() {
        pairs.push((advice_base + column.index(), domain.rotate_omega(x, at)));
    }
    for &(column, at) in cs.instance_queries() {
        if column.index() < nb_committed_instances {
            pairs.push((instance_base + column.index(), domain.rotate_omega(x, at)));
        }
    }

    let x_next = domain.rotate_omega(x, Rotation::next());
    let x_last = domain.rotate_omega(x, Rotation(-((cs.blinding_factors() + 1) as i32)));
    for i in 0..perm_chunks {
        pairs.push((perm_prod_base + i, x));
        pairs.push((perm_prod_base + i, x_next));
    }
    if perm_chunks > 1 {
        for i in (0..perm_chunks - 1).rev() {
            pairs.push((perm_prod_base + i, x_last));
        }
    }

    let mut helper_offset = 0usize;
    for (l_idx, lookup) in cs.lookups().iter().enumerate() {
        pairs.push((lookup_m_base + l_idx, x));
        let chunks = lookup.chunk_by_degree(cs.degree()).num_chunks();
        for j in 0..chunks {
            pairs.push((lookup_helper_base + helper_offset + j, x));
        }
        helper_offset += chunks;
        pairs.push((lookup_acc_base + l_idx, x));
        pairs.push((lookup_acc_base + l_idx, x_next));
    }

    for i in 0..cs.trashcans().len() {
        pairs.push((trash_base + i, x));
    }
    for &(column, at) in cs
        .fixed_queries()
        .iter()
        .filter(|(col, _)| !cs.has_simple_selector_col(col.index()))
    {
        pairs.push((fixed_base + column.index(), domain.rotate_omega(x, at)));
    }
    for i in 0..cs.permutation().get_columns().len() {
        pairs.push((perm_common_base + i, x));
    }
    pairs.push((lin_base, x));

    midnight_proofs::poly::kzg::compute_dummy_queries(&pairs).len()
}
