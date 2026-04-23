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
    /// Concatenated RPN bytecode of every gate polynomial, in iteration
    /// order (`cs.gates().flat_map(|g| g.polynomials())`), each program
    /// terminated by `OP_END`. Consumed by the Solidity bytecode
    /// interpreter via `_evalBytecode` to compute
    /// `partially_evaluate_identities`' gate contributions at x.
    pub gate_bytecode: Vec<u8>,
    /// For each program in `gate_bytecode`, the fixed-column index of
    /// the first simple selector queried by the gate (if any). None is
    /// encoded as 0xFFFFFFFF. Used by
    /// `compute_linearization_commitment` to key the grouping MSM.
    pub gate_selector_cols: Vec<Option<u32>>,
    /// Fixed-column indices that correspond to simple, multiplicative
    /// selectors. These columns' evaluations are implicit 1 (they
    /// aren't transcript-read), but their commitments participate as
    /// distinct points in the linearization MSM.
    pub simple_selector_cols: Vec<u32>,
    /// Total number of gate polynomials (sum over gates of
    /// polynomials.len()). Equal to `gate_selector_cols.len()`.
    pub num_gate_polys: usize,
    /// Per-permutation-column metadata in the exact order returned by
    /// `cs.permutation().get_columns()`. Each entry is
    /// `(column_kind, query_index_at_cur_rotation)` where `column_kind`
    /// is 0 = advice, 1 = fixed, 2 = instance. The Solidity
    /// `_permExpressions` function uses these to look up each column's
    /// evaluation at x inside the main chunk-product constraint.
    pub permutation_columns: Vec<(u8, u16)>,
    /// The chunked structure of `permutation.columns` that the Rust
    /// verifier's `permutation::expressions` walks via
    /// `p.columns.chunks(chunk_len)`. Equal to
    /// `(num_permutation_columns + chunk_len - 1) / chunk_len`. Kept
    /// alongside the column metadata so Solidity doesn't have to
    /// re-derive chunk boundaries.
    pub permutation_chunk_len: usize,
    /// One entry per lookup argument. Each contains the bytecode-
    /// serialised selector, table, and input-expression chunks
    /// needed by Solidity to reconstruct the `logup::Evaluated::
    /// expressions(...)` iterator output.
    pub lookups_bytecode: Vec<LookupBytecode>,
}

/// Serialised (RPN bytecode) form of a single midnight-proofs lookup
/// argument's expression trees. The structure mirrors the Rust
/// `ChunkedArgument` exactly: chunks → parallel_lookups → columns,
/// plus a shared selector + table. Solidity's `_lookupExpressions`
/// walks this in step with the transcript-read evaluations.
#[derive(Clone, Debug)]
pub struct LookupBytecode {
    /// RPN bytecode of the lookup's selector expression (one END).
    pub selector: Vec<u8>,
    /// RPN bytecode of each table-column expression.
    pub table_columns: Vec<Vec<u8>>,
    /// Chunked inputs: `input_chunks[chunk][parallel_lookup][column]`
    /// where each `column` is an RPN bytecode program.
    pub input_chunks: Vec<Vec<Vec<Vec<u8>>>>,
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

        // Serialize every gate polynomial into RPN bytecode + record the
        // gate's simple-selector column (if any) so the linearization MSM
        // on the Solidity side can group by selector.
        let mut gate_bytecode: Vec<u8> = Vec::new();
        let mut gate_selector_cols: Vec<Option<u32>> = Vec::new();
        for gate in cs.gates().iter() {
            let selector_col = gate
                .queried_selectors()
                .iter()
                .filter(|s| s.is_simple())
                .map(|s| s.index() as u32)
                .next();
            for poly in gate.polynomials().iter() {
                gate_bytecode.extend(crate::expr_bytecode::encode_expression(poly));
                gate_selector_cols.push(selector_col);
            }
        }
        let num_gate_polys = gate_selector_cols.len();

        let simple_selector_cols: Vec<u32> = (0..cs.num_fixed_columns())
            .filter(|&i| cs.has_simple_selector_col(i))
            .map(|i| i as u32)
            .collect();

        // Per-permutation-column metadata. The Rust verifier's permutation
        // `expressions` reads each column's evaluation at x via
        // `cs.get_any_query_index(column, Rotation::cur())` then indexes
        // advice_evals/fixed_evals/instance_evals by that query index. Here
        // we replicate the lookup using the public `{advice,fixed,instance}_queries()`
        // accessors so the Solidity side gets a flat (kind, query_idx) array.
        use midnight_proofs::plonk::Any;
        use midnight_proofs::poly::Rotation;
        let permutation_columns: Vec<(u8, u16)> = cs
            .permutation()
            .get_columns()
            .iter()
            .map(|column| {
                let kind: u8 = match column.column_type() {
                    Any::Advice(_) => 0,
                    Any::Fixed => 1,
                    Any::Instance => 2,
                };
                // Find the query index for this column at Rotation::cur().
                let query_idx: usize = match column.column_type() {
                    Any::Advice(_) => cs
                        .advice_queries()
                        .iter()
                        .position(|(c, rot)| {
                            c.index() == column.index() && rot.0 == Rotation::cur().0
                        })
                        .expect("advice column missing cur-rotation query"),
                    Any::Fixed => cs
                        .fixed_queries()
                        .iter()
                        .position(|(c, rot)| {
                            c.index() == column.index() && rot.0 == Rotation::cur().0
                        })
                        .expect("fixed column missing cur-rotation query"),
                    Any::Instance => cs
                        .instance_queries()
                        .iter()
                        .position(|(c, rot)| {
                            c.index() == column.index() && rot.0 == Rotation::cur().0
                        })
                        .expect("instance column missing cur-rotation query"),
                };
                (kind, query_idx as u16)
            })
            .collect();
        let permutation_chunk_len = cs.degree() - 2;

        // Serialise lookup expression trees. Each lookup's selector
        // + table + input chunks gets bytecode-encoded (reusing the
        // gate-bytecode opcode set) so Solidity can re-run the same
        // algorithm that `logup::Evaluated::expressions` uses in Rust.
        let lookups_bytecode: Vec<LookupBytecode> = cs
            .lookups()
            .iter()
            .map(|batched| {
                let chunked = batched.chunk_by_degree(cs.degree());
                let selector = crate::expr_bytecode::encode_expression(chunked.selector_expression());
                let table_columns = chunked
                    .table_expressions()
                    .iter()
                    .map(crate::expr_bytecode::encode_expression)
                    .collect();
                let input_chunks = chunked
                    .input_expression_chunks()
                    .iter()
                    .map(|chunk| {
                        chunk
                            .iter()
                            .map(|parallel_lookup| {
                                parallel_lookup
                                    .iter()
                                    .map(crate::expr_bytecode::encode_expression)
                                    .collect()
                            })
                            .collect()
                    })
                    .collect();
                LookupBytecode { selector, table_columns, input_chunks }
            })
            .collect();

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
            gate_bytecode,
            gate_selector_cols,
            simple_selector_cols,
            num_gate_polys,
            permutation_columns,
            permutation_chunk_len,
            lookups_bytecode,
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

    // Gate bytecode section:
    //   uint32 num_simple_selectors
    //     uint32 col_idx  × num_simple_selectors
    //   uint32 num_gate_polys
    //     for each poly: uint32 selector_col (0xFFFFFFFF for None)
    //   uint32 total_gate_bytecode_len
    //   gate_bytecode bytes
    blob.extend_from_slice(&(vk.simple_selector_cols.len() as u32).to_be_bytes());
    for &c in &vk.simple_selector_cols { blob.extend_from_slice(&c.to_be_bytes()); }
    blob.extend_from_slice(&(vk.num_gate_polys as u32).to_be_bytes());
    for sel in &vk.gate_selector_cols {
        let v: u32 = sel.unwrap_or(0xFFFFFFFF);
        blob.extend_from_slice(&v.to_be_bytes());
    }
    blob.extend_from_slice(&(vk.gate_bytecode.len() as u32).to_be_bytes());
    blob.extend_from_slice(&vk.gate_bytecode);

    // Permutation-expressions metadata:
    //   u32 permutation_chunk_len
    //   u32 num_permutation_columns
    //     { u8 kind (0=advice, 1=fixed, 2=instance), u16 query_idx } × n
    blob.extend_from_slice(&(vk.permutation_chunk_len as u32).to_be_bytes());
    blob.extend_from_slice(&(vk.permutation_columns.len() as u32).to_be_bytes());
    for &(kind, qidx) in &vk.permutation_columns {
        blob.push(kind);
        blob.extend_from_slice(&qidx.to_be_bytes());
    }

    // Lookup-expressions bytecode (Phase A2a):
    //   u32 num_lookups
    //   for each lookup:
    //     u32 selector_len
    //     <selector bytecode>
    //     u32 num_table_cols
    //     for each table col: u32 len, <bytecode>
    //     u32 num_chunks
    //     for each chunk:
    //       u32 num_parallel_lookups
    //       for each parallel lookup:
    //         u32 num_cols
    //         for each col: u32 len, <bytecode>
    append_lookups_section(&mut blob, &vk.lookups_bytecode);

    let total = blob.len();
    let hex_blob = hex::encode(&blob);

    // Emit a minimal contract whose constructor returns the raw blob.
    // The deployed runtime code of the VK contract IS the blob; the
    // verifier retrieves it via `extcodecopy`. This keeps the source
    // very short regardless of how many circuit commitments we store.
    format!(
        "// SPDX-License-Identifier: MIT\n\
pragma solidity ^0.8.24;\n\
\n\
/// @notice Auto-generated minimal verifying key for the poseidon example.\n\
/// @dev The constructor returns a packed byte blob that the verifier reads\n\
/// with `extcodecopy`. The blob layout is fixed by `codegen.rs` and mirrored\n\
/// in `PoseidonVerifier._loadVk`; see that function for the field offsets.\n\
///\n\
/// VK blob size: {total} bytes.\n\
contract PoseidonVerifyingKey {{\n\
    constructor() {{\n\
        bytes memory blob = hex\"{hex_blob}\";\n\
        assembly {{ return(add(blob, 32), mload(blob)) }}\n\
    }}\n\
}}\n"
    )
}

/// Read-only helper that re-emits the entire VK blob as a `bytes memory` so
/// that tests can compare the on-chain VK contract's runtime bytecode with the
/// bytes produced by the codegen. This is purely for diagnostics and is not
/// used by the verifier contract.
pub fn vk_blob(vk: &VkInfo) -> Vec<u8> {
    let mut blob: Vec<u8> = Vec::new();
    blob.extend_from_slice(&vk.transcript_repr_be);
    blob.extend_from_slice(&vk.omega_be);

    let mut c1 = [0u8; 32];
    c1[0..8].copy_from_slice(&vk.n.to_be_bytes());
    c1[8..12].copy_from_slice(&vk.k.to_be_bytes());
    c1[12..16].copy_from_slice(&(vk.num_advice_columns as u32).to_be_bytes());
    c1[16..20].copy_from_slice(&(vk.num_fixed_columns as u32).to_be_bytes());
    c1[20..24].copy_from_slice(&(vk.num_instance_columns as u32).to_be_bytes());
    c1[24..28].copy_from_slice(&(vk.num_challenges as u32).to_be_bytes());
    c1[28..32].copy_from_slice(&(vk.num_phases as u32).to_be_bytes());
    blob.extend_from_slice(&c1);

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

    blob.extend_from_slice(&(vk.simple_selector_cols.len() as u32).to_be_bytes());
    for &c in &vk.simple_selector_cols { blob.extend_from_slice(&c.to_be_bytes()); }
    blob.extend_from_slice(&(vk.num_gate_polys as u32).to_be_bytes());
    for sel in &vk.gate_selector_cols {
        let v: u32 = sel.unwrap_or(0xFFFFFFFF);
        blob.extend_from_slice(&v.to_be_bytes());
    }
    blob.extend_from_slice(&(vk.gate_bytecode.len() as u32).to_be_bytes());
    blob.extend_from_slice(&vk.gate_bytecode);

    blob.extend_from_slice(&(vk.permutation_chunk_len as u32).to_be_bytes());
    blob.extend_from_slice(&(vk.permutation_columns.len() as u32).to_be_bytes());
    for &(kind, qidx) in &vk.permutation_columns {
        blob.push(kind);
        blob.extend_from_slice(&qidx.to_be_bytes());
    }

    append_lookups_section(&mut blob, &vk.lookups_bytecode);

    blob
}

/// Shared serialiser for the lookup bytecode section. Used by both the
/// `PoseidonVerifyingKey.sol` embedding path and the `vk_blob` helper.
fn append_lookups_section(blob: &mut Vec<u8>, lookups: &[LookupBytecode]) {
    blob.extend_from_slice(&(lookups.len() as u32).to_be_bytes());
    for lk in lookups {
        blob.extend_from_slice(&(lk.selector.len() as u32).to_be_bytes());
        blob.extend_from_slice(&lk.selector);
        blob.extend_from_slice(&(lk.table_columns.len() as u32).to_be_bytes());
        for col in &lk.table_columns {
            blob.extend_from_slice(&(col.len() as u32).to_be_bytes());
            blob.extend_from_slice(col);
        }
        blob.extend_from_slice(&(lk.input_chunks.len() as u32).to_be_bytes());
        for chunk in &lk.input_chunks {
            blob.extend_from_slice(&(chunk.len() as u32).to_be_bytes());
            for parallel_lookup in chunk {
                blob.extend_from_slice(&(parallel_lookup.len() as u32).to_be_bytes());
                for col in parallel_lookup {
                    blob.extend_from_slice(&(col.len() as u32).to_be_bytes());
                    blob.extend_from_slice(col);
                }
            }
        }
    }
}
