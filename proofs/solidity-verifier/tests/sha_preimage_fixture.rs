//! End-to-end Solidity verifier coverage for a real zk-stdlib SHA-256
//! preimage circuit. This exercises byte public inputs and the SHA-256 chip
//! family through the generated verifier.

#![cfg(feature = "evm")]

use std::{env, path::Path};

use ff::{Field, PrimeField};
use halo2_solidity_verifier::{
    compile_solidity, pinned_solc_available, CallOutcome, Evm, GeneratorConfig, RenderOptions,
    RenderVk, SolidityGenerator,
};
use midnight_circuits::{
    instructions::{AssignmentInstructions, PublicInputInstructions},
    types::{AssignedByte, Instantiable},
};
use midnight_curves::Fq;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use sha2::Digest;
use sha3::Keccak256;

type F = Fq;

const RUN_EVM_TESTS_ENV: &str = "HALO2_SOLIDITY_RUN_EVM_TESTS";
const K: u32 = 13;

#[derive(Clone, Default)]
struct ShaPreimageCircuit;

impl Relation for ShaPreimageCircuit {
    type Instance = [u8; 32];
    type Witness = [u8; 24];

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(instance.iter().flat_map(AssignedByte::<F>::as_public_input).collect())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned_input = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.sha2_256(layouter, &assigned_input)?;
        output
            .iter()
            .try_for_each(|byte| std_lib.constrain_as_public_input(layouter, byte))
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(ShaPreimageCircuit)
    }
}

#[test]
fn sha_preimage_renders_compiles_and_verifies() {
    if !env_flag_enabled(RUN_EVM_TESTS_ENV) {
        eprintln!("skipping SHA preimage Solidity smoke: set {RUN_EVM_TESTS_ENV}=1 to run it");
        return;
    }

    let srs_dir = srs_dir();
    let srs_path = format!("{srs_dir}/bls_filecoin_2p{K}");
    let fallback_srs_path = format!("{srs_dir}/bls_filecoin_2p19");
    if !Path::new(&srs_path).exists() && !Path::new(&fallback_srs_path).exists() {
        eprintln!(
            "skipping SHA preimage Solidity smoke: SRS not found at {srs_path} or \
             {fallback_srs_path}. Set SRS_DIR or fetch the asset under midfall/zk_stdlib."
        );
        return;
    }
    env::set_var("SRS_DIR", &srs_dir);

    let relation = ShaPreimageCircuit;
    let srs = srs_for_test(&relation, Some(K));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    let witness = deterministic_witness();
    let instance: [u8; 32] = sha2::Sha256::digest(witness).into();
    let instances = ShaPreimageCircuit::format_instance(&instance).expect("format instance");

    let proof = midnight_zk_stdlib::prove::<ShaPreimageCircuit, Keccak256>(
        &srs,
        &pk,
        &relation,
        &instance,
        witness,
        ChaCha8Rng::seed_from_u64(0x051a_5256),
    )
    .expect("SHA preimage proof generation should not fail");

    midnight_zk_stdlib::verify::<ShaPreimageCircuit, Keccak256>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof,
    )
    .expect("native verifier should accept SHA preimage proof");

    let generator = SolidityGenerator::new(&srs, vk.vk(), GeneratorConfig::new(instances.len(), 1));
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .expect("separate SHA preimage render should succeed");
    let verifier_solidity = artifacts.verifier;
    let vk_solidity = artifacts.verifying_key.expect("separate render includes VK");
    let repacked_proof = generator.repack_proof(&proof).expect("proof repack");
    let calldata = generator
        .encode_calldata(&proof, &instances)
        .expect("calldata encoding should succeed");

    let dump_dir = format!(
        "{}/target/sha-preimage-fixture-dump",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::create_dir_all(&dump_dir).ok();
    std::fs::write(format!("{dump_dir}/Halo2Verifier.sol"), &verifier_solidity).ok();
    std::fs::write(format!("{dump_dir}/Halo2VerifyingKey.sol"), &vk_solidity).ok();
    std::fs::write(format!("{dump_dir}/proof.bin"), &proof).ok();
    std::fs::write(format!("{dump_dir}/calldata.bin"), &calldata).ok();
    std::fs::write(format!("{dump_dir}/instances.be"), field_bytes(&instances)).ok();
    eprintln!(
        "[sha_preimage_fixture] proof = {} bytes, repacked = {} bytes, instances = {}, \
         vk_solidity = {} bytes, verifier_solidity = {} bytes; dumps under {dump_dir}",
        proof.len(),
        repacked_proof.len(),
        instances.len(),
        vk_solidity.len(),
        verifier_solidity.len()
    );

    if !pinned_solc_available() {
        eprintln!("skipping SHA preimage EVM smoke: pinned solc not available");
        return;
    }

    let vk_creation_code = compile_solidity(&vk_solidity);
    let verifier_creation_code = compile_solidity(&verifier_solidity);
    let mut evm = Evm::default();
    let vk_address = evm.create(vk_creation_code);
    let verifier_address = evm.create_with_address_arg(verifier_creation_code, vk_address);

    match evm.try_call_with_gas(verifier_address, calldata, 5_000_000_000) {
        CallOutcome::Success {
            gas_used, output, ..
        } => {
            assert_eq!(
                output,
                [vec![0u8; 31], vec![1]].concat(),
                "SHA preimage Solidity verifier should accept the proof; gas_used = {gas_used}, \
                 output = 0x{}",
                hex::encode(&output)
            );
            eprintln!("SHA preimage proof verified on-chain in {gas_used} gas");
        }
        CallOutcome::Revert { gas_used, output } => {
            panic!(
                "SHA preimage Solidity verifier reverted with gas_used = {gas_used}, output = 0x{}",
                hex::encode(&output)
            );
        }
        CallOutcome::Halt { gas_used, reason } => {
            panic!("SHA preimage Solidity verifier halted with gas_used = {gas_used}, reason = {reason}");
        }
    }

    let mut wrong_instances = instances.clone();
    wrong_instances[0] += F::ONE;
    assert_rejects(
        evm.try_call_with_gas(
            verifier_address,
            halo2_solidity_verifier::encode_calldata(&repacked_proof, &wrong_instances),
            5_000_000_000,
        ),
        "wrong SHA public byte",
    );

    let mut bad_proof = repacked_proof;
    bad_proof[0] ^= 0x01;
    assert_rejects(
        evm.try_call_with_gas(
            verifier_address,
            halo2_solidity_verifier::encode_calldata(&bad_proof, &instances),
            5_000_000_000,
        ),
        "mutated SHA proof",
    );
}

fn deterministic_witness() -> [u8; 24] {
    *b"midfall-sha-preimage-e2e"
}

fn field_bytes(instances: &[F]) -> Vec<u8> {
    instances.iter().flat_map(|value| value.to_repr().as_ref().to_vec()).collect()
}

fn assert_rejects(outcome: CallOutcome, context: &str) {
    match outcome {
        CallOutcome::Success { output, .. } => {
            assert_eq!(
                output,
                vec![0u8; 32],
                "{context} should return false or revert"
            );
        }
        CallOutcome::Revert { .. } | CallOutcome::Halt { .. } => {}
    }
}

fn srs_dir() -> String {
    env::var("SRS_DIR").unwrap_or_else(|_| {
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../zk_stdlib/examples/assets"
        )
        .to_string()
    })
}

fn env_flag_enabled(name: &str) -> bool {
    env::var(name)
        .map(|value| {
            matches!(
                value.to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        })
        .unwrap_or(false)
}
