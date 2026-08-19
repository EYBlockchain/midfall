//! End-to-end Solidity verifier coverage for a real zk-stdlib RSA signature
//! circuit. This exercises the biguint/range-check circuit family rather than
//! another Poseidon-only shape.

#![cfg(feature = "evm")]

use std::{env, ops::Rem, path::Path};

use ff::{Field, PrimeField};
use halo2_solidity_verifier::{
    compile_solidity, pinned_solc_available, revm::primitives::Address, CallOutcome, Evm,
    GeneratorConfig, RenderOptions, RenderVk, SolidityGenerator,
};
use midnight_circuits::{biguint::AssignedBigUint, instructions::AssertionInstructions};
use midnight_curves::Fq;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use num_bigint::BigUint;
use num_traits::{Num, One};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use sha3::Keccak256;

type F = Fq;
type Modulus = BigUint;
type Message = BigUint;
type Signature = BigUint;
type PublicKey = Modulus;

const RUN_EVM_TESTS_ENV: &str = "HALO2_SOLIDITY_RUN_EVM_TESTS";
const K: u32 = 12;
const NB_BITS: u32 = 1024;
const RSA_E: u64 = 3;

#[derive(Clone, Default)]
struct RsaSignatureCircuit;

impl Relation for RsaSignatureCircuit {
    type Instance = (PublicKey, Message);
    type Witness = Signature;

    fn format_instance((public_key, message): &Self::Instance) -> Result<Vec<F>, Error> {
        Ok([
            AssignedBigUint::<F>::as_public_input(public_key, NB_BITS),
            AssignedBigUint::<F>::as_public_input(message, NB_BITS),
        ]
        .into_iter()
        .flatten()
        .collect())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let biguint = std_lib.biguint();

        let public_key = biguint.assign_biguint(
            layouter,
            instance.as_ref().map(|(public_key, _)| public_key.clone()),
            NB_BITS,
        )?;
        let message =
            biguint.assign_biguint(layouter, instance.map(|(_, message)| message), NB_BITS)?;
        let signature = biguint.assign_biguint(layouter, witness, NB_BITS)?;

        biguint.constrain_as_public_input(layouter, &public_key, NB_BITS)?;
        biguint.constrain_as_public_input(layouter, &message, NB_BITS)?;

        let expected_message = biguint.mod_exp(layouter, &signature, RSA_E, &public_key)?;
        biguint.assert_equal(layouter, &message, &expected_message)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(RsaSignatureCircuit)
    }
}

#[test]
fn rsa_signature_renders_compiles_and_verifies() {
    if !env_flag_enabled(RUN_EVM_TESTS_ENV) {
        eprintln!("skipping RSA signature Solidity smoke: set {RUN_EVM_TESTS_ENV}=1 to run it");
        return;
    }

    let srs_dir = srs_dir();
    let srs_path = format!("{srs_dir}/bls_filecoin_2p{K}");
    let fallback_srs_path = format!("{srs_dir}/bls_filecoin_2p19");
    // The gate was explicitly requested, so a missing asset fails rather than
    // silently reporting a pass that rendered and compiled nothing.
    assert!(
        Path::new(&srs_path).exists() || Path::new(&fallback_srs_path).exists(),
        "{RUN_EVM_TESTS_ENV}=1 requires the test SRS, but it was not found at {srs_path} or \
         {fallback_srs_path}.
Fetch it with:
    curl -L -o {fallback_srs_path} \
         https://midnight-s3-fileshare-dev-eu-west-1.s3.eu-west-1.amazonaws.com/bls_filecoin_2p19
or point SRS_DIR at an existing copy."
    );
    env::set_var("SRS_DIR", &srs_dir);

    let relation = RsaSignatureCircuit;
    let srs = srs_for_test(&relation, Some(K));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    let (instance, witness) = deterministic_rsa_instance();
    let instances = RsaSignatureCircuit::format_instance(&instance).expect("format instance");

    let proof = midnight_zk_stdlib::prove::<RsaSignatureCircuit, Keccak256>(
        &srs,
        &pk,
        &relation,
        &instance,
        witness,
        ChaCha8Rng::seed_from_u64(0x5eed_cafe),
    )
    .expect("RSA proof generation should not fail");

    midnight_zk_stdlib::verify::<RsaSignatureCircuit, Keccak256>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof,
    )
    .expect("native verifier should accept RSA proof");

    let generator = SolidityGenerator::new(&srs, vk.vk(), GeneratorConfig::new(instances.len(), 1));
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .expect("separate RSA render should succeed");
    let verifier_solidity = artifacts.verifier;
    let vk_solidity = artifacts.verifying_key.expect("separate render includes VK");
    let repacked_proof = generator.repack_proof(&proof).expect("proof repack");
    let calldata = generator
        .encode_calldata(&proof, &instances)
        .expect("calldata encoding should succeed");

    let dump_dir = format!(
        "{}/target/rsa-signature-fixture-dump",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::create_dir_all(&dump_dir).ok();
    std::fs::write(format!("{dump_dir}/Halo2Verifier.sol"), &verifier_solidity).ok();
    std::fs::write(format!("{dump_dir}/Halo2VerifyingKey.sol"), &vk_solidity).ok();
    std::fs::write(format!("{dump_dir}/proof.bin"), &proof).ok();
    std::fs::write(format!("{dump_dir}/calldata.bin"), &calldata).ok();
    std::fs::write(format!("{dump_dir}/instances.be"), field_bytes(&instances)).ok();
    eprintln!(
        "[rsa_signature_fixture] proof = {} bytes, repacked = {} bytes, instances = {}, \
         vk_solidity = {} bytes, verifier_solidity = {} bytes; dumps under {dump_dir}",
        proof.len(),
        repacked_proof.len(),
        instances.len(),
        vk_solidity.len(),
        verifier_solidity.len()
    );

    assert!(
        pinned_solc_available(),
        "{RUN_EVM_TESTS_ENV}=1 requires the pinned solc, which was not found or did not match.
\
         Install it, point SOLC at the binary, or set \
         HALO2_SOLIDITY_ALLOW_UNPINNED_SOLC=1 to accept another version."
    );

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
                "RSA Solidity verifier should accept the proof; gas_used = {gas_used}, \
                 output = 0x{}",
                hex::encode(&output)
            );
            eprintln!("RSA signature proof verified on-chain in {gas_used} gas");
        }
        CallOutcome::Revert { gas_used, output } => {
            panic!(
                "RSA Solidity verifier reverted with gas_used = {gas_used}, output = 0x{}",
                hex::encode(&output)
            );
        }
        CallOutcome::Halt { gas_used, reason } => {
            panic!("RSA Solidity verifier halted with gas_used = {gas_used}, reason = {reason}");
        }
    }

    let mut wrong_instances = instances.clone();
    wrong_instances[0] += F::ONE;
    let wrong_calldata =
        halo2_solidity_verifier::encode_calldata(&repacked_proof, &wrong_instances);
    assert_rejects(
        evm.try_call_with_gas(verifier_address, wrong_calldata, 5_000_000_000),
        "wrong RSA public instance",
    );

    let mut bad_proof = repacked_proof.clone();
    bad_proof[0] ^= 0x01;
    let bad_proof_calldata = halo2_solidity_verifier::encode_calldata(&bad_proof, &instances);
    assert_rejects(
        evm.try_call_with_gas(verifier_address, bad_proof_calldata, 5_000_000_000),
        "mutated RSA proof",
    );

    assert_adversarial_calldata_variants_rejected(
        &mut evm,
        verifier_address,
        &repacked_proof,
        &instances,
        &calldata,
        "RSA",
    );
}

fn deterministic_rsa_instance() -> ((PublicKey, Message), Signature) {
    let p = BigUint::from_str_radix(
        "81e05798232330a8c7059621c812dc9d2bba37edbd0e79f101eef1db373c12724595480ae6a9dbbf158fa65d6910b8aea7b3be2eede9123ede8d84ec9e8ee907",
        16,
    )
    .unwrap();
    let q = BigUint::from_str_radix(
        "acd6fd3c0d70502e8ecefb20259fbf4783a614a0fb1a33701e3adc84947326a754f8a632e5f6cd718a681cde953024b3612bb0646f180b6fd063b1ef4e10d4a5",
        16,
    )
    .unwrap();
    let phi = (&p - BigUint::one()) * (&q - BigUint::one());
    let d = BigUint::from(RSA_E).modinv(&phi).expect("RSA exponent invertible");
    let public_key = &p * &q;
    let message = BigUint::from_str_radix(
        "7d3318ef1f6d18cb933fdf1fd37bb0ab87217305d2e908a705ca8a7a27815a9a",
        16,
    )
    .unwrap()
    .rem(&public_key);
    let signature = message.modpow(&d, &public_key);
    ((public_key, message), signature)
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
