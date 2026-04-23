//! Generates the two Solidity artefacts for the poseidon example:
//!
//! * [`render_verifying_key`] — `PoseidonVerifyingKey.sol`, a minimal
//!   constants-only contract whose constructor returns a packed byte blob
//!   with the circuit-specific VK data (fixed commitments, permutation
//!   commitments, transcript_repr, G2 s·g2 for the pairing, domain sizes).
//! * [`render_verifier`] — `PoseidonVerifier.sol`, the verifier logic. The
//!   verifier implements the Keccak256 Fiat-Shamir transcript, the EIP-2537
//!   BLS12-381 precompile wrappers (G1ADD, G1MSM, PAIRING) and the per-phase
//!   proof-stream skeleton that mirrors the Rust `parse_trace`,
//!   `verify_algebraic_constraints` and `KZGCommitmentScheme::multi_prepare`.

use midnight_curves::{Bls12, Fq, G2Affine};
use midnight_proofs::{
    plonk::VerifyingKey as PlonkVk,
    poly::kzg::{params::ParamsKZG, KZGCommitmentScheme},
};

use crate::eip2537::{fq_to_be, g1_projective_to_eip2537, g2_to_eip2537};

/// Information extracted from the runtime VK that is baked into the generated
/// Solidity. This keeps the VK contract compact (everything lives in a bytes
/// blob returned by the constructor) while the Verifier contract reads the
/// structural constants it needs.
pub struct VkInfo {
    /// log2(n).
    pub k: u32,
    /// Domain size n = 2^k.
    pub n: u64,
    /// ω, the n-th root of unity (BE 32 bytes).
    pub omega_be: [u8; 32],
    /// transcript_repr — the Blake2b digest of the VK that is hashed into the
    /// transcript at the start of verification.
    pub transcript_repr_be: [u8; 32],
    /// Number of advice columns.
    pub num_advice_columns: usize,
    /// Number of fixed columns (after selector -> fixed conversion).
    pub num_fixed_columns: usize,
    /// Number of committed instance columns (always 0 for the poseidon
    /// example). Normal instance columns = num_instance_columns.
    pub num_instance_columns: usize,
    /// Number of challenges the transcript produces per phase.
    pub num_challenges: usize,
    /// Number of phases in the circuit.
    pub num_phases: usize,
    /// Constraint-system degree (max gate degree).
    pub cs_degree: usize,
    /// Number of simple multiplicative selectors (these are implicit 1 at
    /// evaluation points, so are *not* read from the transcript).
    pub num_simple_selectors: usize,
    /// Blinding factors (affects l_0 / l_last / l_blind ranges).
    pub blinding_factors: usize,
    /// Number of advice queries (= fp-sized transcript reads after x is squeezed).
    pub num_advice_queries: usize,
    /// Number of fixed queries (minus simple selectors).
    pub num_fixed_queries: usize,
    /// Number of instance queries (normal).
    pub num_instance_queries: usize,
    /// Number of lookup arguments.
    pub num_lookups: usize,
    /// For each lookup, the number of chunks (== # helper polys). Total
    /// lookup commitments per proof = sum(num_chunks) + num_lookups
    /// (one accumulator per lookup). Total lookup evals per proof =
    /// num_lookups * 2 + sum(num_chunks) (1 m_eval + 1 acc_eval +
    /// 1 acc_next_eval + num_chunks helper_evals).
    pub lookup_num_chunks: Vec<usize>,
    /// Number of trashcan arguments.
    pub num_trashcans: usize,
    /// For each instance query on a column whose index is within the
    /// committed-instance range, the verifier reads the evaluation from the
    /// transcript. This field counts how many such transcript reads happen.
    pub num_committed_instance_evals: usize,
    /// Number of columns in the permutation argument.
    pub num_permutation_columns: usize,
    /// Number of permutation-product commitments (chunked).
    pub num_permutation_chunks: usize,
    /// Number of quotient limbs committed to by the prover.
    pub num_quotient_limbs: usize,
    /// Fixed commitments (EIP-2537 encoded, 128 bytes each).
    pub fixed_comms_eip2537: Vec<[u8; 128]>,
    /// Permutation commitments (EIP-2537 encoded).
    pub perm_comms_eip2537: Vec<[u8; 128]>,
    /// s·G2 for the pairing (EIP-2537 encoded, 256 bytes).
    pub s_g2_eip2537: [u8; 256],
    /// -G2 (negated generator) for the pairing's lhs.
    pub neg_g2_eip2537: [u8; 256],
}

impl VkInfo {
    /// Extract all the data we need from a live VK + SRS.
    pub fn from_live(
        vk: &PlonkVk<Fq, KZGCommitmentScheme<Bls12>>,
        srs: &ParamsKZG<Bls12>,
    ) -> Self {
        let cs = vk.cs();
        let domain = vk.get_domain();

        let fixed_comms_eip2537 = vk
            .fixed_commitments()
            .iter()
            .map(g1_projective_to_eip2537)
            .collect::<Vec<_>>();
        let perm_comms_eip2537 = vk
            .permutation()
            .commitments()
            .iter()
            .map(g1_projective_to_eip2537)
            .collect::<Vec<_>>();

        let s_g2 = srs.s_g2();
        let s_g2_eip2537 = g2_to_eip2537(&G2Affine::from(s_g2));
        let neg_g2_eip2537 = {
            use group::Group;
            let neg_g2: midnight_curves::G2Projective =
                -<midnight_curves::G2Projective as Group>::generator();
            g2_to_eip2537(&G2Affine::from(neg_g2))
        };

        // Without the `single-h-commitment` feature (which is the default),
        // the prover writes one commitment per quotient limb.
        let nb_quotient_coms = domain.get_quotient_poly_degree();

        let num_simple_selectors = cs.num_simple_selectors();
        let num_fixed_queries = cs
            .fixed_queries()
            .iter()
            .filter(|(col, _)| !cs.has_simple_selector_col(col.index()))
            .count();
        let num_phases = cs.advice_column_phase().iter().max().copied().unwrap_or(0) as usize + 1;

        let permutation_chunks = {
            let chunk_len = cs.degree() - 2;
            let cols = cs.permutation().get_columns().len();
            if cols == 0 { 0 } else { (cols + chunk_len - 1) / chunk_len }
        };

        let lookup_num_chunks: Vec<usize> = cs
            .lookups()
            .iter()
            .map(|l| l.chunk_by_degree(cs.degree()).num_chunks())
            .collect();

        // zk_stdlib always passes exactly 1 committed instance per proof, so
        // the committed-instance column range is [0, 1). Every instance query
        // on that column is a transcript read in the verifier.
        let nb_committed_instances = 1usize;
        let num_committed_instance_evals = cs
            .instance_queries()
            .iter()
            .filter(|(col, _)| col.index() < nb_committed_instances)
            .count();

        Self {
            k: domain.k(),
            n: vk.n(),
            omega_be: {
                let mut le = domain.get_omega().to_repr_le_32();
                le.reverse();
                le
            },
            transcript_repr_be: fq_to_be(&vk.transcript_repr()),
            num_advice_columns: cs.num_advice_columns(),
            num_fixed_columns: cs.num_fixed_columns(),
            num_instance_columns: cs.num_instance_columns(),
            num_challenges: cs.num_challenges(),
            num_phases,
            cs_degree: cs.degree(),
            num_simple_selectors,
            blinding_factors: cs.blinding_factors(),
            num_advice_queries: cs.advice_queries().len(),
            num_fixed_queries,
            num_instance_queries: cs.instance_queries().len(),
            num_lookups: cs.lookups().len(),
            lookup_num_chunks,
            num_trashcans: cs.trashcans().len(),
            num_committed_instance_evals,
            num_permutation_columns: cs.permutation().get_columns().len(),
            num_permutation_chunks: permutation_chunks,
            num_quotient_limbs: nb_quotient_coms,
            fixed_comms_eip2537,
            perm_comms_eip2537,
            s_g2_eip2537,
            neg_g2_eip2537,
        }
    }
}

// Helper: some versions of the scalar type may not expose `to_repr_le_32`
// directly. Provide an extension trait so we can keep the codegen concise.
trait ToReprLe32 {
    fn to_repr_le_32(&self) -> [u8; 32];
}
impl ToReprLe32 for Fq {
    fn to_repr_le_32(&self) -> [u8; 32] {
        use ff::PrimeField;
        self.to_repr()
    }
}



/// Render the `PoseidonVerifyingKey.sol` contract — a tiny constants-only
/// contract whose constructor returns a packed byte blob. The verifier reads
/// this blob to initialise its runtime constants.
pub fn render_verifying_key(vk: &VkInfo) -> String {
    // Layout of the blob (all big-endian, all 32/64/128/256-byte aligned):
    //   [0      .. 32)  transcript_repr (Fq, BE padded to 32)
    //   [32     .. 64)  omega           (Fq, BE)
    //   [64     .. 96)  packed constants:
    //                     uint64 n, uint32 k, uint32 num_advice_columns,
    //                     uint32 num_fixed_columns,  uint32 num_instance_columns,
    //                     uint32 num_challenges, uint32 num_phases
    //                     (zero padded to 32)
    //   [96     .. 128) packed constants 2:
    //                     uint32 cs_degree, uint32 num_simple_selectors,
    //                     uint32 blinding_factors, uint32 num_advice_queries,
    //                     uint32 num_fixed_queries, uint32 num_instance_queries,
    //                     uint32 num_lookups, uint32 num_trashcans
    //   [128    .. 160) packed constants 3:
    //                     uint32 num_permutation_columns, uint32 num_permutation_chunks,
    //                     uint32 num_quotient_limbs, (rest zero)
    //   [160    ..    ) fixed_comms (each 128 bytes EIP-2537)
    //   [    ..       ) perm_comms (each 128 bytes)
    //   [    ..       ) s_g2        (256 bytes)
    //   [    ..       ) neg_g2      (256 bytes)

    let mut blob: Vec<u8> = Vec::new();
    blob.extend_from_slice(&vk.transcript_repr_be);
    blob.extend_from_slice(&vk.omega_be);

    // constants 1
    let mut c1 = [0u8; 32];
    c1[0..8].copy_from_slice(&vk.n.to_be_bytes());
    c1[8..12].copy_from_slice(&vk.k.to_be_bytes());
    c1[12..16].copy_from_slice(&(vk.num_advice_columns as u32).to_be_bytes());
    c1[16..20].copy_from_slice(&(vk.num_fixed_columns as u32).to_be_bytes());
    c1[20..24].copy_from_slice(&(vk.num_instance_columns as u32).to_be_bytes());
    c1[24..28].copy_from_slice(&(vk.num_challenges as u32).to_be_bytes());
    c1[28..32].copy_from_slice(&(vk.num_phases as u32).to_be_bytes());
    blob.extend_from_slice(&c1);

    // constants 2
    let mut c2 = [0u8; 32];
    c2[0..4].copy_from_slice(&(vk.cs_degree as u32).to_be_bytes());
    c2[4..8].copy_from_slice(&(vk.num_simple_selectors as u32).to_be_bytes());
    c2[8..12].copy_from_slice(&(vk.blinding_factors as u32).to_be_bytes());
    c2[12..16].copy_from_slice(&(vk.num_advice_queries as u32).to_be_bytes());
    c2[16..20].copy_from_slice(&(vk.num_fixed_queries as u32).to_be_bytes());
    c2[20..24].copy_from_slice(&(vk.num_instance_queries as u32).to_be_bytes());
    c2[24..28].copy_from_slice(&(vk.num_lookups as u32).to_be_bytes());
    c2[28..32].copy_from_slice(&(vk.num_trashcans as u32).to_be_bytes());
    blob.extend_from_slice(&c2);

    // constants 3
    let total_lookup_helpers: u32 =
        vk.lookup_num_chunks.iter().map(|&c| c as u32).sum();
    let mut c3 = [0u8; 32];
    c3[0..4].copy_from_slice(&(vk.num_permutation_columns as u32).to_be_bytes());
    c3[4..8].copy_from_slice(&(vk.num_permutation_chunks as u32).to_be_bytes());
    c3[8..12].copy_from_slice(&(vk.num_quotient_limbs as u32).to_be_bytes());
    c3[12..16].copy_from_slice(&total_lookup_helpers.to_be_bytes());
    c3[16..20].copy_from_slice(&(vk.num_committed_instance_evals as u32).to_be_bytes());
    blob.extend_from_slice(&c3);

    for c in &vk.fixed_comms_eip2537 { blob.extend_from_slice(c); }
    for c in &vk.perm_comms_eip2537  { blob.extend_from_slice(c); }
    blob.extend_from_slice(&vk.s_g2_eip2537);
    blob.extend_from_slice(&vk.neg_g2_eip2537);

    let total = blob.len();

    // Emit the contract as a single mstore-per-word assembly block, just like
    // the Halo2VerifyingKey template in halo2-solidity-verifier.
    let mut body = String::new();
    body.push_str(&format!("    constructor() {{\n        assembly {{\n"));
    for (i, chunk) in blob.chunks(32).enumerate() {
        let mut word = [0u8; 32];
        word[..chunk.len()].copy_from_slice(chunk);
        body.push_str(&format!(
            "            mstore({:#06x}, 0x{})\n",
            i * 32,
            hex::encode(word)
        ));
    }
    body.push_str(&format!("            return(0, {:#06x})\n", total));
    body.push_str("        }\n    }\n");

    format!(
        "// SPDX-License-Identifier: MIT\npragma solidity ^0.8.24;\n\n\
         // Auto-generated from midnight-proofs VerifyingKey (poseidon example).\n\
         // Total VK blob size: {total} bytes.\n\
         contract PoseidonVerifyingKey {{\n{body}}}\n",
    )
}
