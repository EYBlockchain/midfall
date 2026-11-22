// SPDX-License-Identifier: CC0-1.0
//! OBJ.11 / OBJ.12 (WP B5): export the F1 generator's BUILD_ID inputs and
//! re-render the tracked artifact with the reference generator.
//!
//! WHY THIS TEST EXISTS. `Halo2Verifier.sol` and `Halo2VerifyingKey.sol` in
//! `target/poseidon-fixture-dump/` are tracked, and the Lean generator is
//! required to reproduce them byte for byte (OBJ.12). Two of the six BUILD_ID
//! preimage components are not derivable from the tracked fixture bundle:
//!
//!   * `SOLIDITY_VERIFIER_FEATURES` - `build.rs` folds `CARGO_FEATURE_*` into
//!     the crate at compile time (ART:125); which subset produced the dump is
//!     recorded nowhere the tree can read.
//!   * `srs_fingerprint` - VK:73-92 hashes `n`, `g2`, `s_g2` and `[tau]G1` of
//!     the SRS actually loaded. The SRS file is an external asset.
//!
//! This test runs the reference generator on the SAME circuit, SRS and config
//! as `tests/poseidon_fixture.rs`, renders the separate-VK pair WITHOUT
//! generating a proof (the proof is non-deterministic and irrelevant to the
//! text), and writes a `build.json` next to the artifacts carrying the two
//! inputs above plus the SRS digest and the artifact hashes. `formal/scripts/
//! artifact_gate.sh` consumes it, and the Lean gate
//! `GeneratedKats.artifact_gate_poseidon` pins the same values.
//!
//! RUN IT (from `proofs/solidity-verifier`, the pinned toolchain is in
//! `rust-toolchain.toml`):
//!
//! ```text
//! SRS_DIR=../.srs cargo test --features truncated-challenges \
//!     --test artifact_export -- --nocapture
//! ```
//!
//! It runs under `truncated-challenges` alone: the deployed dump carries the
//! x3 mask (D:1449), and the `evm` feature is not needed to render text. The
//! emitted feature string is the crate's OWN `CARGO_FEATURE_*` list, so the
//! value in `build.json` is measured, not asserted.
//!
//! MODES.
//!   * default: write `$MIDFALL_ARTIFACT_OUT` (or `target/artifact-export/`)
//!     and PRINT the comparison against the tracked dump;
//!   * `MIDFALL_ARTIFACT_GATE=1`: FAIL on any byte difference, printing the
//!     first differing line. This is the mode `artifact_gate.sh` uses.

#![cfg(feature = "truncated-challenges")]

use std::{env, fs, path::{Path, PathBuf}};

use ff::Field;
use group::{Curve, Group};
use halo2_solidity_verifier::{
    GeneratorConfig, RenderOptions, RenderVk, SolidityGenerator, __test_only_g1_to_u256s,
    __test_only_g2_to_u256s,
};
use midnight_circuits::instructions::{
    hash::HashCPU, AssignmentInstructions, PublicInputInstructions,
};
use midnight_curves::{Bls12, Fq, G1Projective};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{Error, VerifyingKey},
    poly::kzg::{params::ParamsKZG, KZGCommitmentScheme},
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use sha2::Sha256;
use sha3::{Digest, Keccak256};

type F = Fq;
type Vk = VerifyingKey<F, KZGCommitmentScheme<Bls12>>;
type Params = ParamsKZG<Bls12>;

const K: u32 = 6;
const NUM_INSTANCES: usize = 1;
const NUM_COMMITTED_INSTANCES: usize = 1;

/// The fixture's circuit, copied from `tests/poseidon_fixture.rs` (the test
/// that wrote the tracked dump) so this exporter renders the same object.
#[derive(Clone, Default)]
struct PoseidonExample;

impl Relation for PoseidonExample {
    type Instance = F;
    type Witness = [F; 3];

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned_message = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.poseidon(layouter, &assigned_message)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch { poseidon: true, ..ZkStdLibArch::default() }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonExample)
    }
}

fn srs_dir() -> String {
    env::var("SRS_DIR").unwrap_or_else(|_| {
        concat!(env!("CARGO_MANIFEST_DIR"), "/../../zk_stdlib/examples/assets").to_string()
    })
}

/// VK:73-92, reproduced with the crate's own public encoders. The preimage is
/// exactly what `VerifierBuildInputs::srs_fingerprint` hashes: the domain-size
/// `n`, both G2 points in the generator's EIP-2537 word order, and `[tau]G1`
/// recomputed from the Lagrange basis the commitments use.
fn srs_fingerprint(srs: &Params, vk: &Vk) -> [u8; 32] {
    let g_lagrange = srs.g_lagrange();
    let omega = vk.get_domain().get_omega();
    let mut omega_pow = F::ONE;
    let omega_powers: Vec<F> = (0..g_lagrange.len())
        .map(|_| {
            let current = omega_pow;
            omega_pow *= omega;
            current
        })
        .collect();
    let tau_g1 = G1Projective::multi_exp(g_lagrange, &omega_powers).to_affine();

    let mut hasher = Keccak256::new();
    hasher.update(b"halo2-solidity-verifier-srs-v1");
    hasher.update((g_lagrange.len() as u64).to_be_bytes());
    for word in __test_only_g2_to_u256s(&srs.g2().to_affine()) {
        hasher.update(word.to_be_bytes::<32>());
    }
    for word in __test_only_g2_to_u256s(&srs.s_g2().to_affine()) {
        hasher.update(word.to_be_bytes::<32>());
    }
    for word in __test_only_g1_to_u256s(&tau_g1) {
        hasher.update(word.to_be_bytes::<32>());
    }
    hasher.finalize().into()
}

fn srs_sha256(srs: &Params) -> String {
    let mut buf = Vec::new();
    srs.write_custom(&mut buf, SerdeFormat::Processed)
        .expect("serialize the SRS for its digest");
    hex::encode(Sha256::digest(&buf))
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

fn first_diff_line(a: &str, b: &str) -> Option<(usize, String, String)> {
    let al: Vec<&str> = a.split('\n').collect();
    let bl: Vec<&str> = b.split('\n').collect();
    let n = al.len().max(bl.len());
    for i in 0..n {
        let x = al.get(i).copied().unwrap_or("<missing>");
        let y = bl.get(i).copied().unwrap_or("<missing>");
        if x != y {
            return Some((i + 1, x.to_string(), y.to_string()));
        }
    }
    None
}

fn out_dir() -> PathBuf {
    if let Ok(dir) = env::var("MIDFALL_ARTIFACT_OUT") {
        return PathBuf::from(dir);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/artifact-export")
}

#[test]
fn poseidon_artifact_export_and_gate() {
    let srs_dir = srs_dir();
    let srs_path = Path::new(&srs_dir).join(format!("bls_filecoin_2p{K}"));
    let fallback = Path::new(&srs_dir).join("bls_filecoin_2p19");
    if !srs_path.exists() && !fallback.exists() {
        panic!(
            "artifact export needs the F1 SRS: neither {srs_path:?} nor {fallback:?} exists. \
             Run scripts/ensure_srs_assets.sh --srs-dir <dir> and set SRS_DIR, or leave the \
             gate NOT-COMPUTABLE - do not report it green."
        );
    }
    env::set_var("SRS_DIR", &srs_dir);

    let relation = PoseidonExample;
    let srs = srs_for_test(&relation, Some(K));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);

    let generator = SolidityGenerator::new(
        &srs,
        vk.vk(),
        GeneratorConfig::new(NUM_INSTANCES, NUM_COMMITTED_INSTANCES),
    );
    let artifacts = generator
        .render(RenderOptions { vk: RenderVk::Separate, ..RenderOptions::default() })
        .expect("separate render should succeed");
    let verifier = artifacts.verifier;
    let verifying_key = artifacts.verifying_key.expect("separate render includes VK");

    let fingerprint = srs_fingerprint(&srs, vk.vk());
    let features = env!("SOLIDITY_VERIFIER_FEATURES");
    let srs_digest = srs_sha256(&srs);
    let srs_bytes = {
        let mut buf = Vec::new();
        srs.write_custom(&mut buf, SerdeFormat::Processed).unwrap();
        buf.len()
    };

    let dir = out_dir();
    fs::create_dir_all(&dir).expect("create artifact output directory");
    fs::write(dir.join("Halo2Verifier.sol"), &verifier).unwrap();
    fs::write(dir.join("Halo2VerifyingKey.sol"), &verifying_key).unwrap();

    let shown = |s: &str| {
        // `wc -m`-style character count: the unit the Lean gates pin.
        s.chars().count()
    };
    let build = serde_json::json!({
        "schema": 2,
        "card": "OBJ.11 / OBJ.12 (WP B5)",
        "generator": "proofs/solidity-verifier tests/artifact_export.rs",
        "circuit": "PoseidonExample",
        "k": K,
        "num_instances": NUM_INSTANCES,
        "num_committed_instances": NUM_COMMITTED_INSTANCES,
        "render_vk": "separate",
        "truncated_challenges": true,
        "trace": false,
        "gas_checkpoints": false,
        "provenance": serde_json::Value::Null,
        "features": features,
        "features_len": features.len(),
        "srs_fingerprint_hex": hex::encode(fingerprint),
        "srs_sha256": srs_digest,
        "srs_serialized_bytes": srs_bytes,
        "srs_len": srs.g_lagrange().len(),
        "srs_dir": srs_dir,
        "verifier": {
            "bytes": verifier.len(),
            "chars": shown(&verifier),
            "lines": verifier.split('\n').count(),
            "sha256": sha256_hex(verifier.as_bytes()),
        },
        "verifying_key": {
            "bytes": verifying_key.len(),
            "chars": shown(&verifying_key),
            "lines": verifying_key.split('\n').count(),
            "sha256": sha256_hex(verifying_key.as_bytes()),
        },
    });
    let build_text = serde_json::to_string_pretty(&build).unwrap() + "\n";
    fs::write(dir.join("build.json"), &build_text).unwrap();

    println!("artifact_export: OUTPUT_DIR={}", dir.display());
    println!(
        "artifact_export: features={features:?} (len {}) srs_fingerprint=0x{} srs_sha256={}",
        features.len(),
        hex::encode(fingerprint),
        sha256_hex(build_text.as_bytes())
    );
    println!(
        "artifact_export: Halo2Verifier.sol bytes={} chars={} lines={} sha256={}",
        verifier.len(),
        shown(&verifier),
        verifier.split('\n').count(),
        sha256_hex(verifier.as_bytes())
    );
    println!(
        "artifact_export: Halo2VerifyingKey.sol bytes={} chars={} lines={} sha256={}",
        verifying_key.len(),
        shown(&verifying_key),
        verifying_key.split('\n').count(),
        sha256_hex(verifying_key.as_bytes())
    );

    // Compare against the tracked reference. The comparison is byte for byte;
    // the sha256 above is printed for the report, never used as the equality.
    let reference = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/poseidon-fixture-dump");
    let ref_verifier = fs::read(reference.join("Halo2Verifier.sol")).expect("tracked verifier");
    let ref_vk = fs::read(reference.join("Halo2VerifyingKey.sol")).expect("tracked VK");
    let gate = env::var("MIDFALL_ARTIFACT_GATE").as_deref() == Ok("1");

    let mut mismatched = false;
    for (name, rendered, tracked) in [
        ("Halo2Verifier.sol", verifier.as_bytes(), ref_verifier.as_slice()),
        ("Halo2VerifyingKey.sol", verifying_key.as_bytes(), ref_vk.as_slice()),
    ] {
        if rendered == tracked {
            println!(
                "artifact_export: {name} MATCHES tracked ({} bytes, sha256 {})",
                tracked.len(),
                sha256_hex(tracked)
            );
        } else {
            mismatched = true;
            println!(
                "artifact_export: {name} DIFFERS tracked: rendered {} bytes / sha256 {}, tracked {} bytes / sha256 {}",
                rendered.len(),
                sha256_hex(rendered),
                tracked.len(),
                sha256_hex(tracked)
            );
            let rs = String::from_utf8_lossy(rendered);
            let ts = String::from_utf8_lossy(tracked);
            if let Some((line, a, b)) = first_diff_line(&rs, &ts) {
                println!("artifact_export: first differing line {line}\n  rendered: {a}\n  tracked:  {b}");
            }
        }
    }
    println!(
        "artifact_export: comparison {}",
        if mismatched { "MISMATCH" } else { "IDENTICAL" }
    );
    if gate && mismatched {
        panic!(
            "artifacts differ from the tracked reference; see the lines above and {}",
            dir.display()
        );
    }
}
