//! End-to-end Solidity verifier coverage for a real zk-stdlib SHA-256
//! preimage circuit. This exercises byte public inputs and the SHA-256 chip
//! family through the generated verifier.

#![cfg(feature = "evm")]

use std::{env, path::Path};

use ff::{Field, PrimeField};
use halo2_solidity_verifier::{
    compile_solidity, pinned_solc_available, revm::primitives::Address, CallOutcome, Evm,
    GeneratorConfig, RenderOptions, RenderVk, SolidityGenerator,
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
        ChaCha8Rng::seed_from_u64(0x51a5_256),
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

    match evm.try_call_with_gas(verifier_address, calldata.clone(), 5_000_000_000) {
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

    let mut bad_proof = repacked_proof.clone();
    bad_proof[0] ^= 0x01;
    assert_rejects(
        evm.try_call_with_gas(
            verifier_address,
            halo2_solidity_verifier::encode_calldata(&bad_proof, &instances),
            5_000_000_000,
        ),
        "mutated SHA proof",
    );

    assert_adversarial_calldata_variants_rejected(
        &mut evm,
        verifier_address,
        &repacked_proof,
        &instances,
        &calldata,
        "SHA preimage",
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

fn assert_adversarial_calldata_variants_rejected(
    evm: &mut Evm,
    verifier_address: Address,
    proof: &[u8],
    instances: &[F],
    valid_calldata: &[u8],
    context: &str,
) {
    let mut cases = Vec::<(String, Vec<u8>)>::new();

    let mut wrong_selector = valid_calldata.to_vec();
    wrong_selector[0] ^= 0x01;
    cases.push(("wrong selector".to_string(), wrong_selector));

    let mut trailing_bytes = valid_calldata.to_vec();
    trailing_bytes.extend_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    cases.push(("trailing bytes".to_string(), trailing_bytes));

    cases.push((
        "truncated calldata".to_string(),
        valid_calldata[..valid_calldata.len() - 1].to_vec(),
    ));
    cases.push((
        "empty proof".to_string(),
        halo2_solidity_verifier::encode_calldata(&[], instances),
    ));

    let mut proof_length_too_long = valid_calldata.to_vec();
    overwrite_u256_word(
        &mut proof_length_too_long,
        proof_len_word_start(),
        proof.len() as u64 + 1,
    );
    cases.push(("proof length too long".to_string(), proof_length_too_long));

    let mut proof_length_too_short = valid_calldata.to_vec();
    overwrite_u256_word(
        &mut proof_length_too_short,
        proof_len_word_start(),
        proof.len() as u64 - 1,
    );
    cases.push(("proof length too short".to_string(), proof_length_too_short));

    let mut instance_length_too_long = valid_calldata.to_vec();
    overwrite_u256_word(
        &mut instance_length_too_long,
        instances_len_word_start(proof),
        instances.len() as u64 + 1,
    );
    cases.push((
        "instance array length too long".to_string(),
        instance_length_too_long,
    ));

    let mut instance_length_too_short = valid_calldata.to_vec();
    overwrite_u256_word(
        &mut instance_length_too_short,
        instances_len_word_start(proof),
        instances.len() as u64 - 1,
    );
    cases.push((
        "instance array length too short".to_string(),
        instance_length_too_short,
    ));

    let mut noncanonical_instance = valid_calldata.to_vec();
    noncanonical_instance
        [first_instance_word_start(proof)..first_instance_word_start(proof) + 0x20]
        .copy_from_slice(&fr_modulus_be_word());
    cases.push((
        "public instance equal to Fr modulus".to_string(),
        noncanonical_instance,
    ));

    let mut public_byte_256 = valid_calldata.to_vec();
    overwrite_u256_word(&mut public_byte_256, first_instance_word_start(proof), 256);
    cases.push(("public byte encoded as 256".to_string(), public_byte_256));

    let mut proof_head_overlap = valid_calldata.to_vec();
    overwrite_u256_word(&mut proof_head_overlap, 0x04, 0x20);
    cases.push((
        "proof head overlaps ABI head".to_string(),
        proof_head_overlap,
    ));

    let mut proof_head_shifted_without_gap = valid_calldata.to_vec();
    overwrite_u256_word(&mut proof_head_shifted_without_gap, 0x04, 0x60);
    cases.push((
        "proof head shifted without matching gap".to_string(),
        proof_head_shifted_without_gap,
    ));

    let mut instances_head_overlap = valid_calldata.to_vec();
    overwrite_u256_word(&mut instances_head_overlap, 0x24, 0x40);
    cases.push((
        "instances head overlaps proof".to_string(),
        instances_head_overlap,
    ));

    let mut instances_head_shifted = valid_calldata.to_vec();
    overwrite_u256_word(
        &mut instances_head_shifted,
        0x24,
        canonical_instances_head(proof) as u64 + 0x20,
    );
    cases.push(("instances head shifted".to_string(), instances_head_shifted));

    for (name, calldata) in cases {
        assert_rejects(
            evm.try_call_with_gas(verifier_address, calldata, 5_000_000_000),
            &format!("{context} adversarial calldata: {name}"),
        );
    }
}

fn overwrite_u256_word(bytes: &mut [u8], start: usize, value: u64) {
    bytes[start..start + 32].fill(0);
    bytes[start + 24..start + 32].copy_from_slice(&value.to_be_bytes());
}

fn fr_modulus_be_word() -> [u8; 32] {
    hex::decode("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001")
        .expect("fr modulus hex")
        .try_into()
        .expect("Fr modulus is one word")
}

fn proof_len_word_start() -> usize {
    4 + 0x40
}

fn canonical_instances_head(proof: &[u8]) -> usize {
    0x40 + 0x20 + proof.len()
}

fn instances_len_word_start(proof: &[u8]) -> usize {
    4 + canonical_instances_head(proof)
}

fn first_instance_word_start(proof: &[u8]) -> usize {
    instances_len_word_start(proof) + 0x20
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
