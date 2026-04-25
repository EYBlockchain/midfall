//! Generate Solidity contracts + minimal fixture files for the IVC
//! single-circuit aggregation chain (mirrors
//! `aggregation/examples/single_circuit_aggregation.rs`).
//!
//! Running `cargo run --bin generate_ivc` will:
//!   1. Build inner SHA-256 SRS / VK / PK (k=13, Filecoin SRS).
//!   2. Generate `STEPS=3` random SHA-256 preimage proofs.
//!   3. Set up the IVC at `IVC_K` (default 19, Midnight SRS), drive
//!      `STEPS - 1` Poseidon-transcript chain steps and one final
//!      `sha3::Keccak256`-transcript step.
//!   4. Dump the final-step proof, the corresponding flat public-input
//!      vector, and the IVC VK blob to `fixtures/ivc/`.
//!   5. Render `contracts/circuits/ivc/IvcVerifyingKey.sol` from the
//!      live VK structure.
//!
//! End-to-end runtime is dominated by the IVC chain:
//!   * inner SHA-256 keygen + 3 inner proofs: ~1 s
//!   * IVC keygen (k=19): ~20 s
//!   * 3 IVC steps (each Poseidon or Keccak): ~30 s each
//!
//! Total: 90-120 s in release.  This is why the fixture is checked in
//! and only regenerated when explicitly requested.
//!
//! Environment variables:
//!   * `IVC_K`    — log2 of the IVC circuit's domain size (default `19`).
//!   * `SRS_DIR`  — KZG trusted-setup directory (see ARCHITECTURE.md §5).

use std::{fs, path::PathBuf};

use midnight_curves::Fq;
use midnight_solidity_verifier::{
    circuits::ivc::IvcAggregationFixture,
    codegen::{render_verifying_key_named, vk_blob, VkInfo},
    eip2537::fq_to_be,
};

const CIRCUIT_NAME: &str = "ivc";
const CONTRACT_NAME: &str = "IvcVerifyingKey";

fn main() {
    let here: PathBuf = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .expect("CARGO_MANIFEST_DIR");

    let fixtures = here.join("fixtures").join(CIRCUIT_NAME);
    let circuit_contracts = here.join("contracts").join("circuits").join(CIRCUIT_NAME);
    fs::create_dir_all(&fixtures).expect("mkdir fixtures");
    fs::create_dir_all(&circuit_contracts).expect("mkdir circuit contracts dir");

    let ivc_k: u32 = std::env::var("IVC_K")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);

    eprintln!("[1/4] driving IVC chain (3 inner proofs aggregated, final step Keccak256)");
    eprintln!("      NB: full chain at k=19 takes ~90-120 s in release.");
    let fx = IvcAggregationFixture::build(ivc_k);

    eprintln!("[2/4] extracting VK info");
    let vk_info = VkInfo::from_live(fx.vk.vk(), &fx.srs);

    eprintln!(
        "      k={} n={} cs_degree={} blinding={}\n      \
         fixed_cols={} perm_cols={} advice_cols={} inst_cols={} \
         challenges={} phases={} simple_sels={}\n      \
         advice_q={} fixed_q={} inst_q={}\n      \
         lookups={} trashcans={} perm_chunks={} quotient_limbs={}\n      \
         num_public_inputs={} proof_size={} bytes",
        vk_info.k,
        vk_info.n,
        vk_info.cs_degree,
        vk_info.blinding_factors,
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
        fx.public_inputs.len(),
        fx.proof.len(),
    );

    // Same simple-selector position == column-index invariant the
    // generic Solidity verifier relies on (see ARCHITECTURE.md §7.2,
    // bin/generate_rsa.rs).  Surface a clear panic at codegen time if
    // a future change to the IVC circuit ever violates it.
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
    fs::write(circuit_contracts.join(format!("{CONTRACT_NAME}.sol")), sol).expect("write sol");

    eprintln!("[4/4] dumping proof + instance + vk blob");
    fs::write(fixtures.join("proof.bin"), &fx.proof).expect("write proof");

    // instance.bin: u64 BE count followed by `count * 32` bytes BE.
    {
        let limbs: &[Fq] = &fx.public_inputs;
        let mut blob = Vec::with_capacity(8 + 32 * limbs.len());
        blob.extend_from_slice(&(limbs.len() as u64).to_be_bytes());
        for v in limbs {
            blob.extend_from_slice(&fq_to_be(v));
        }
        fs::write(fixtures.join("instance.bin"), &blob).expect("write instance.bin");
        eprintln!("      instance blob: {} limbs ({} bytes)", limbs.len(), blob.len());
    }

    fs::write(fixtures.join("vk.bin"), vk_blob(&vk_info)).expect("write vk blob");

    eprintln!(
        "OK — see {}/ for the generated VK contract",
        circuit_contracts.display()
    );
    eprintln!("      {}/ for fixtures", fixtures.display());
}
