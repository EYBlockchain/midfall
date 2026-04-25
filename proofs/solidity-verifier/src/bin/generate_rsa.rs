//! Generate Solidity contracts + minimal fixture files for the
//! `zk_stdlib/examples/rsa_signature.rs` circuit.
//!
//! Running `cargo run --bin generate_rsa` will:
//!   1. Build the SRS (k=12 by default), keygen VK/PK, and prove the
//!      RSA-signature circuit using the Keccak256 transcript.
//!   2. Dump the proof, instance (flat Fq-limb concat), and VK blob to
//!      `fixtures/rsa_signature/`.
//!   3. Render
//!      `contracts/circuits/rsa_signature/RsaSignatureVerifyingKey.sol`
//!      with the runtime data.
//!
//! This is a Phase 1 deliverable. The emitted artefacts do NOT yet
//! verify against the current `contracts/PoseidonVerifier.sol` because
//! that contract bakes in six poseidon-specific assumptions
//! (ARCHITECTURE.md §7.2). Phase 2-5 lifts those one by one; the
//! fixtures produced here serve as the acceptance target.
//!
//! Environment variables:
//!   * `RSA_K`    — log2 of the domain size (default `12`).
//!   * `RSA_SEED` — prover + message RNG seed (default `1`).
//!   * `SRS_DIR`  — KZG trusted-setup directory (see
//!                  `proofs/solidity-verifier/ARCHITECTURE.md` §5).

use std::{fs, path::PathBuf};

use midnight_solidity_verifier::{
    circuits::rsa_signature::{RsaSignatureExample, RsaSignatureFixture},
    codegen::{render_verifying_key_named, vk_blob, VkInfo},
    eip2537::fq_to_be,
};

const CIRCUIT_NAME: &str = "rsa_signature";
const CONTRACT_NAME: &str = "RsaSignatureVerifyingKey";

fn main() {
    let here: PathBuf = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .expect("CARGO_MANIFEST_DIR");

    let fixtures = here.join("fixtures").join(CIRCUIT_NAME);
    let circuit_contracts = here.join("contracts").join("circuits").join(CIRCUIT_NAME);
    fs::create_dir_all(&fixtures).expect("mkdir fixtures");
    fs::create_dir_all(&circuit_contracts).expect("mkdir circuit contracts dir");

    let k = std::env::var("RSA_K")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(12u32);
    let seed: u64 = std::env::var("RSA_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);

    eprintln!("[1/4] building RSA-signature proof (k={k}, seed={seed})");
    eprintln!("      NB: this runs a full KZG prover pass over a k={k} circuit;");
    eprintln!("          expect ~1-3 minutes in release, longer in debug.");
    let fx = RsaSignatureFixture::build(k, seed);

    eprintln!("[2/4] extracting VK info");
    let vk_info = VkInfo::from_live(fx.vk.vk(), &fx.srs);

    eprintln!(
        "      k={} n={} cs_degree={} blinding={}\n      fixed_cols={} perm_cols={} advice_cols={} inst_cols={} challenges={} phases={} simple_sels={}\n      advice_q={} fixed_q={} inst_q={}\n      lookups={} trashcans={} perm_chunks={} quotient_limbs={}\n      proof_size={} bytes",
        vk_info.k, vk_info.n, vk_info.cs_degree, vk_info.blinding_factors,
        vk_info.num_fixed_columns,
        vk_info.num_permutation_columns,
        vk_info.num_advice_columns,
        vk_info.num_instance_columns,
        vk_info.num_challenges,
        vk_info.num_phases,
        vk_info.num_simple_selectors,
        vk_info.num_advice_queries,
        vk_info.num_fixed_queries,
        vk_info.num_instance_queries,
        vk_info.num_lookups,
        vk_info.num_trashcans,
        vk_info.num_permutation_chunks,
        vk_info.num_quotient_limbs,
        fx.proof.len(),
    );

    // Phase 3 invariant check: `_buildFixedEvalsFull` on the Solidity
    // side relies on midnight-proofs' "query position == column index
    // for simple-selector queries" invariant; abort if a future
    // circuit violates it so the offending VK never ships.
    {
        let cs = fx.vk.vk().cs();
        for (pos, (col, _rot)) in cs.fixed_queries().iter().enumerate() {
            if cs.has_simple_selector_col(col.index()) && col.index() != pos {
                panic!(
                    "Simple-selector query at position {pos} points to col \
                     {col_idx}; the Solidity `_buildFixedEvalsFull` assumes \
                     position == col for simple selectors and will silently \
                     misalign transcript evals otherwise.",
                    col_idx = col.index()
                );
            }
        }
    }

    eprintln!("[3/4] writing Solidity VK contract");
    let sol = render_verifying_key_named(&vk_info, CONTRACT_NAME);
    fs::write(
        circuit_contracts.join(format!("{CONTRACT_NAME}.sol")),
        sol,
    )
    .expect("write sol");

    eprintln!("[4/4] dumping proof + instance + vk blob");
    fs::write(fixtures.join("proof.bin"), &fx.proof).expect("write proof");

    // Flat instance file: all public-input Fq limbs concatenated BE.
    //
    // `format_instance((pk, msg))` returns the pk and msg decompositions
    // flattened into a single Vec<Fq>; we dump each limb as a 32-byte
    // big-endian element preceded by a u64 BE count so the Solidity
    // side can reconstruct the Lagrange inner product once that path is
    // wired up in Phase 2.
    {
        use midnight_zk_stdlib::Relation;
        let limbs = <RsaSignatureExample as Relation>::format_instance(&fx.instance)
            .expect("format_instance");
        let mut blob = Vec::with_capacity(8 + 32 * limbs.len());
        blob.extend_from_slice(&(limbs.len() as u64).to_be_bytes());
        for v in &limbs {
            blob.extend_from_slice(&fq_to_be(v));
        }
        fs::write(fixtures.join("instance.bin"), &blob).expect("write instance.bin");
        eprintln!("      instance blob: {} limbs ({} bytes)", limbs.len(), blob.len());
    }

    // Dump the VK blob separately so future tests don't have to deploy the
    // VK contract when they just want to cross-check the byte layout.
    fs::write(fixtures.join("vk.bin"), vk_blob(&vk_info)).expect("write vk blob");

    eprintln!(
        "OK — see {}/ for the generated VK contract",
        circuit_contracts.display()
    );
    eprintln!("      {}/ for fixtures", fixtures.display());
}
