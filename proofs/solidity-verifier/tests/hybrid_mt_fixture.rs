//! End-to-end Solidity verifier coverage for the zk-stdlib hybrid Merkle-tree
//! opening example. This is a larger circuit than the existing Poseidon/SHA
//! smokes: it hashes a 32-byte leaf with SHA-256 and then walks a 64-level
//! Poseidon tree.

#![cfg(feature = "evm")]

use std::{env, path::Path};

use ff::{Field, PrimeField};
use halo2_solidity_verifier::{
    compile_solidity, pinned_solc_available, revm::primitives::Address, CallOutcome, Evm,
    GeneratorConfig, RenderOptions, RenderVk, SolidityGenerator,
};
use midnight_circuits::{
    hash::poseidon::{constants::PoseidonField, PoseidonChip},
    instructions::{
        hash::HashCPU, ArithInstructions, AssignmentInstructions, ControlFlowInstructions,
        ConversionInstructions, DecompositionInstructions, PublicInputInstructions,
    },
    types::{AssignedBit, AssignedNative},
};
use midnight_curves::Fq;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use sha2::Digest;
use sha3::Keccak256;

type F = Fq;

const RUN_EVM_TESTS_ENV: &str = "HALO2_SOLIDITY_RUN_EVM_TESTS";
const K: u32 = 13;
const TREE_HEIGHT: usize = 64;
const INPUT_BYTES: usize = 32;

#[derive(Clone, Copy, Debug)]
enum Position {
    Left,
    Right,
}

impl From<Position> for F {
    fn from(value: Position) -> Self {
        match value {
            Position::Left => F::ZERO,
            Position::Right => F::ONE,
        }
    }
}

#[derive(Clone, Debug)]
struct MerklePath<F>
where
    F: PrimeField,
{
    leaf_bytes: [u8; INPUT_BYTES],
    siblings: [(F, Position); TREE_HEIGHT - 1],
}

impl<F: PoseidonField> MerklePath<F> {
    fn compute_root(&self) -> F {
        let digest = sha2::Sha256::digest(self.leaf_bytes);
        let digest: [F; 2] = digest
            .chunks(16)
            .map(|bytes| u128::from_be_bytes(bytes.try_into().unwrap()))
            .map(F::from_u128)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let leaf = <PoseidonChip<F> as HashCPU<F, F>>::hash(&[digest[0], digest[1], F::ZERO]);
        self.siblings.iter().fold(leaf, |acc, (sibling, position)| match position {
            Position::Left => <PoseidonChip<F> as HashCPU<F, F>>::hash(&[*sibling, acc, F::ZERO]),
            Position::Right => <PoseidonChip<F> as HashCPU<F, F>>::hash(&[acc, *sibling, F::ZERO]),
        })
    }
}

#[derive(Clone, Default)]
struct HybridMtCircuit;

impl Relation for HybridMtCircuit {
    type Instance = F;
    type Witness = MerklePath<F>;

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
        let input_bytes = witness.clone().map(|path| path.leaf_bytes).transpose_vec(INPUT_BYTES);
        let assigned_input_bytes = std_lib.assign_many(layouter, input_bytes.as_slice())?;

        let output = std_lib.sha2_256(layouter, &assigned_input_bytes)?;
        let output_words = output
            .chunks_exact(4)
            .map(|word_bytes| std_lib.assigned_from_be_bytes(layouter, word_bytes))
            .collect::<Result<Vec<_>, _>>()?;

        let lo = std_lib.linear_combination(
            layouter,
            &[
                (F::from_u128(2u128.pow(96)), output_words[0].clone()),
                (F::from_u128(2u128.pow(64)), output_words[1].clone()),
                (F::from_u128(2u128.pow(32)), output_words[2].clone()),
                (F::ONE, output_words[3].clone()),
            ],
            F::ZERO,
        )?;
        let hi = std_lib.linear_combination(
            layouter,
            &[
                (F::from_u128(2u128.pow(96)), output_words[4].clone()),
                (F::from_u128(2u128.pow(64)), output_words[5].clone()),
                (F::from_u128(2u128.pow(32)), output_words[6].clone()),
                (F::ONE, output_words[7].clone()),
            ],
            F::ZERO,
        )?;

        let zero: AssignedNative<F> = std_lib.assign_fixed(layouter, F::ZERO)?;
        let leaf = std_lib.poseidon(layouter, &[lo, hi, zero.clone()])?;

        let assigned_siblings = std_lib.assign_many(
            layouter,
            witness
                .clone()
                .map(|path| path.siblings.iter().map(|(sibling, _)| *sibling).collect::<Vec<_>>())
                .transpose_vec(TREE_HEIGHT - 1)
                .as_slice(),
        )?;
        let assigned_positions = std_lib.assign_many(
            layouter,
            witness
                .map(|path| {
                    path.siblings.iter().map(|(_, position)| F::from(*position)).collect::<Vec<_>>()
                })
                .transpose_vec(TREE_HEIGHT - 1)
                .as_slice(),
        )?;
        let assigned_positions = assigned_positions
            .iter()
            .map(|position| std_lib.convert(layouter, position))
            .collect::<Result<Vec<AssignedBit<F>>, Error>>()?;

        let root = assigned_siblings.iter().zip(assigned_positions.iter()).try_fold(
            leaf,
            |acc, (sibling, position)| {
                let left = std_lib.select(layouter, position, &acc, sibling)?;
                let right = std_lib.select(layouter, position, sibling, &acc)?;
                std_lib.poseidon(layouter, &[left, right, zero.clone()])
            },
        )?;

        std_lib.constrain_as_public_input(layouter, &root)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            sha2_256: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(HybridMtCircuit)
    }
}

#[test]
fn hybrid_mt_renders_compiles_and_verifies() {
    if !env_flag_enabled(RUN_EVM_TESTS_ENV) {
        eprintln!("skipping hybrid MT Solidity smoke: set {RUN_EVM_TESTS_ENV}=1 to run it");
        return;
    }

    let srs_dir = srs_dir();
    let srs_path = format!("{srs_dir}/bls_filecoin_2p{K}");
    let fallback_srs_path = format!("{srs_dir}/bls_filecoin_2p19");
    if !Path::new(&srs_path).exists() && !Path::new(&fallback_srs_path).exists() {
        eprintln!(
            "skipping hybrid MT Solidity smoke: SRS not found at {srs_path} or \
             {fallback_srs_path}. Set SRS_DIR or fetch the asset under midfall/zk_stdlib."
        );
        return;
    }
    env::set_var("SRS_DIR", &srs_dir);

    let relation = HybridMtCircuit;
    let srs = srs_for_test(&relation, Some(K));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
    let witness = deterministic_merkle_path();
    let instance = witness.compute_root();
    let instances = HybridMtCircuit::format_instance(&instance).expect("format instance");

    let proof = midnight_zk_stdlib::prove::<HybridMtCircuit, Keccak256>(
        &srs,
        &pk,
        &relation,
        &instance,
        witness,
        ChaCha8Rng::seed_from_u64(0x64_7aee),
    )
    .expect("hybrid MT proof generation should not fail");

    midnight_zk_stdlib::verify::<HybridMtCircuit, Keccak256>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof,
    )
    .expect("native verifier should accept hybrid MT proof");

    let generator = SolidityGenerator::new(&srs, vk.vk(), GeneratorConfig::new(instances.len(), 1));
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .expect("separate hybrid MT render should succeed");
    let verifier_solidity = artifacts.verifier;
    let vk_solidity = artifacts.verifying_key.expect("separate render includes VK");
    let repacked_proof = generator.repack_proof(&proof).expect("proof repack");
    let calldata = generator
        .encode_calldata(&proof, &instances)
        .expect("calldata encoding should succeed");

    let dump_dir = format!(
        "{}/target/hybrid-mt-fixture-dump",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::create_dir_all(&dump_dir).ok();
    std::fs::write(format!("{dump_dir}/Halo2Verifier.sol"), &verifier_solidity).ok();
    std::fs::write(format!("{dump_dir}/Halo2VerifyingKey.sol"), &vk_solidity).ok();
    std::fs::write(format!("{dump_dir}/proof.bin"), &proof).ok();
    std::fs::write(format!("{dump_dir}/calldata.bin"), &calldata).ok();
    std::fs::write(format!("{dump_dir}/instances.be"), field_bytes(&instances)).ok();
    eprintln!(
        "[hybrid_mt_fixture] proof = {} bytes, repacked = {} bytes, instances = {}, \
         vk_solidity = {} bytes, verifier_solidity = {} bytes; dumps under {dump_dir}",
        proof.len(),
        repacked_proof.len(),
        instances.len(),
        vk_solidity.len(),
        verifier_solidity.len()
    );

    if !pinned_solc_available() {
        eprintln!("skipping hybrid MT EVM smoke: pinned solc not available");
        return;
    }

    let vk_creation_code = compile_solidity(&vk_solidity);
    let verifier_creation_code = compile_solidity(&verifier_solidity);
    let mut evm = Evm::default();
    let vk_address = evm.create(vk_creation_code);
    let verifier_address = evm.create_with_address_arg(verifier_creation_code, vk_address);

    assert_accepts(
        evm.try_call_with_gas(verifier_address, calldata.clone(), 5_000_000_000),
        "valid hybrid MT proof",
    );

    let mut wrong_instances = instances.clone();
    wrong_instances[0] += F::ONE;
    assert_rejects(
        evm.try_call_with_gas(
            verifier_address,
            halo2_solidity_verifier::encode_calldata(&repacked_proof, &wrong_instances),
            5_000_000_000,
        ),
        "wrong hybrid MT root",
    );

    let mut bad_proof = repacked_proof.clone();
    bad_proof[0] ^= 0x01;
    assert_rejects(
        evm.try_call_with_gas(
            verifier_address,
            halo2_solidity_verifier::encode_calldata(&bad_proof, &instances),
            5_000_000_000,
        ),
        "mutated hybrid MT proof",
    );

    assert_adversarial_calldata_variants_rejected(
        &mut evm,
        verifier_address,
        &repacked_proof,
        &instances,
        &calldata,
    );
}

fn deterministic_merkle_path() -> MerklePath<F> {
    let mut rng = ChaCha8Rng::seed_from_u64(0x647a_ee00);
    let leaf_bytes = core::array::from_fn(|_| rng.gen::<u8>());
    let siblings = core::array::from_fn(|idx| {
        let sibling = F::random(&mut rng);
        let position = if idx % 3 == 0 {
            Position::Left
        } else {
            Position::Right
        };
        (sibling, position)
    });
    MerklePath {
        leaf_bytes,
        siblings,
    }
}

fn assert_accepts(outcome: CallOutcome, context: &str) {
    match outcome {
        CallOutcome::Success {
            gas_used, output, ..
        } => {
            assert_eq!(
                output,
                [vec![0u8; 31], vec![1]].concat(),
                "{context} should return true; gas_used = {gas_used}, output = 0x{}",
                hex::encode(&output)
            );
            eprintln!("{context} verified on-chain in {gas_used} gas");
        }
        CallOutcome::Revert { gas_used, output } => {
            panic!(
                "{context} reverted with gas_used = {gas_used}, output = 0x{}",
                hex::encode(output)
            );
        }
        CallOutcome::Halt { gas_used, reason } => {
            panic!("{context} halted with gas_used = {gas_used}, reason = {reason}");
        }
    }
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
) {
    let mut wrong_selector = valid_calldata.to_vec();
    wrong_selector[0] ^= 0x01;

    let mut trailing_bytes = valid_calldata.to_vec();
    trailing_bytes.extend_from_slice(&[0xde, 0xad, 0xbe, 0xef]);

    let mut instance_length_too_long = valid_calldata.to_vec();
    overwrite_u256_word(
        &mut instance_length_too_long,
        instances_len_word_start(proof),
        instances.len() as u64 + 1,
    );

    let mut noncanonical_instance = valid_calldata.to_vec();
    noncanonical_instance
        [first_instance_word_start(proof)..first_instance_word_start(proof) + 0x20]
        .copy_from_slice(&fr_modulus_be_word());

    for (name, calldata) in [
        ("wrong selector", wrong_selector),
        ("trailing bytes", trailing_bytes),
        (
            "truncated calldata",
            valid_calldata[..valid_calldata.len() - 1].to_vec(),
        ),
        ("instance array length too long", instance_length_too_long),
        ("public instance equal to Fr modulus", noncanonical_instance),
    ] {
        assert_rejects(
            evm.try_call_with_gas(verifier_address, calldata, 5_000_000_000),
            &format!("hybrid MT adversarial calldata: {name}"),
        );
    }
}

fn field_bytes(instances: &[F]) -> Vec<u8> {
    instances.iter().flat_map(|value| value.to_repr().as_ref().to_vec()).collect()
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
