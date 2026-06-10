#![no_main]

use std::{cell::RefCell, ops::Range, sync::LazyLock};

use halo2_solidity_verifier::{
    compile_solidity, encode_calldata, CallOutcome, Evm, GeneratorConfig, RenderOptions,
    RepackError, SolidityGenerator, FN_SIG_VERIFY_PROOF,
};
use libfuzzer_sys::fuzz_target;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        create_proof, keygen_pk, keygen_vk_with_k, Advice, Circuit, Column, ConstraintSystem,
        Constraints, Error, Selector,
    },
    poly::{kzg::params::ParamsKZG, kzg::KZGCommitmentScheme, Rotation},
    transcript::{CircuitTranscript, Transcript},
};
use rand_chacha::{rand_core::SeedableRng, ChaCha8Rng};

const K: u32 = 5;
const SELECTOR_BYTES: usize = 4;
const WORD_BYTES: usize = 32;
const G1_BYTES: usize = 128;
const PROOF_HEAD_CPTR: usize = SELECTOR_BYTES;
const INSTANCES_HEAD_CPTR: usize = SELECTOR_BYTES + WORD_BYTES;
const PROOF_LEN_CPTR: usize = SELECTOR_BYTES + 2 * WORD_BYTES;
const PROOF_CPTR: usize = SELECTOR_BYTES + 3 * WORD_BYTES;
const MAX_RAW_CALLDATA: usize = 8192;

struct FuzzFixture {
    verifier_creation_code: Vec<u8>,
    valid_calldata: Vec<u8>,
    proof_len: usize,
    num_instance_cptr: usize,
    proof_g1_ranges: Vec<Range<usize>>,
    eval_ranges: Vec<Range<usize>>,
    q_eval_ranges: Vec<Range<usize>>,
    instance_ranges: Vec<Range<usize>>,
}

static FIXTURE: LazyLock<FuzzFixture> = LazyLock::new(build_fixture);

thread_local! {
    static DEPLOYED: RefCell<DeployedVerifier> = RefCell::new(DeployedVerifier::deploy(&FIXTURE));
}

struct DeployedVerifier {
    evm: Evm,
    verifier_address: halo2_solidity_verifier::revm::primitives::Address,
}

impl DeployedVerifier {
    fn deploy(fixture: &FuzzFixture) -> Self {
        let mut evm = Evm::default();
        let verifier_address = evm.create(fixture.verifier_creation_code.clone());
        let mut deployed = Self {
            evm,
            verifier_address,
        };
        let output = deployed.call(fixture.valid_calldata.clone());
        assert!(
            output_is_true(output.as_deref()),
            "generated Solidity verifier must accept the seed proof before fuzzing"
        );
        deployed
    }

    fn call(&mut self, calldata: Vec<u8>) -> Option<Vec<u8>> {
        match self.evm.try_call_with_gas(self.verifier_address, calldata, 500_000_000) {
            CallOutcome::Success { output, .. } => Some(output),
            CallOutcome::Revert { .. } | CallOutcome::Halt { .. } => None,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct MiniCircuit;

#[derive(Clone, Debug)]
struct MiniConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    out: Column<Advice>,
    selector: Selector,
}

impl Circuit<Fq> for MiniCircuit {
    type Config = MiniConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn params(&self) -> Self::Params {}

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let out = meta.advice_column();
        let committed_instance = meta.instance_column();
        let public_instance = meta.instance_column();
        let selector = meta.selector();

        meta.create_gate("mini public balance", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let out = meta.query_advice(out, Rotation::cur());
            let committed = meta.query_instance(committed_instance, Rotation::cur());
            let public = meta.query_instance(public_instance, Rotation::cur());

            Constraints::with_selector(
                selector,
                vec![("public balance", a + b + committed + public - out)],
            )
        });

        MiniConfig {
            a,
            b,
            out,
            selector,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "mini witness",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                region.assign_advice(|| "a", config.a, 0, || Value::known(Fq::from(3)))?;
                region.assign_advice(|| "b", config.b, 0, || Value::known(Fq::from(4)))?;
                region.assign_advice(|| "out", config.out, 0, || Value::known(Fq::from(7)))?;
                Ok(())
            },
        )
    }
}

fn build_fixture() -> FuzzFixture {
    let mut setup_rng = ChaCha8Rng::seed_from_u64(0x501d_f077);
    let params = ParamsKZG::<Bls12>::unsafe_setup(K, &mut setup_rng);
    let circuit = MiniCircuit;
    let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, K)
        .expect("mini circuit VK generation");
    let pk = keygen_pk(vk, &circuit).expect("mini circuit PK generation");

    let committed = [Fq::from(0)];
    let public = [Fq::from(0)];
    let all_instance_columns: [&[Fq]; 2] = [&committed, &public];
    let mut proof_rng = ChaCha8Rng::seed_from_u64(0x51d1_f1ed);
    let mut transcript = CircuitTranscript::<sha3::Keccak256>::init();
    create_proof::<Fq, KZGCommitmentScheme<Bls12>, _, _>(
        &params,
        &pk,
        std::slice::from_ref(&circuit),
        1,
        &[&all_instance_columns],
        &mut proof_rng,
        &mut transcript,
    )
    .expect("mini proof generation");
    let compressed_proof = transcript.finalize();

    let generator = SolidityGenerator::new(&params, pk.get_vk(), GeneratorConfig::new(1, 1));
    let layout = match generator.repack_proof(&[]) {
        Err(RepackError::LengthMismatch {
            expected,
            prefix_g1,
            num_evals,
            num_point_sets,
            ..
        }) => {
            assert_eq!(
                compressed_proof.len(),
                expected,
                "repack length oracle must match generated proof"
            );
            RepackedLayout {
                prefix_g1,
                num_evals,
                num_point_sets,
            }
        }
        other => panic!("expected repack length mismatch for empty proof, got {other:?}"),
    };
    let proof = generator.repack_proof(&compressed_proof).expect("proof repack");
    assert_eq!(
        proof.len(),
        layout.repacked_len(),
        "repacked proof length should match layout oracle"
    );
    let valid_calldata = encode_calldata(&proof, &public);
    let verifier_solidity = generator
        .render(RenderOptions::default())
        .expect("embedded verifier render")
        .verifier;
    let verifier_creation_code = compile_solidity(verifier_solidity);
    let num_instance_cptr = PROOF_CPTR + proof.len();
    let instance_cptr = num_instance_cptr + WORD_BYTES;

    let mut proof_g1_ranges = Vec::new();
    for idx in 0..layout.prefix_g1 {
        push_range(&mut proof_g1_ranges, PROOF_CPTR + idx * G1_BYTES, G1_BYTES);
    }
    let eval_offset = PROOF_CPTR + layout.prefix_g1 * G1_BYTES;
    let eval_ranges = word_ranges(eval_offset, layout.num_evals);
    let f_com_cptr = eval_offset + layout.num_evals * WORD_BYTES;
    push_range(&mut proof_g1_ranges, f_com_cptr, G1_BYTES);
    let q_eval_cptr = f_com_cptr + G1_BYTES;
    let q_eval_ranges = word_ranges(q_eval_cptr, layout.num_point_sets);
    let pi_cptr = q_eval_cptr + layout.num_point_sets * WORD_BYTES;
    push_range(&mut proof_g1_ranges, pi_cptr, G1_BYTES);
    assert_eq!(pi_cptr + G1_BYTES, num_instance_cptr);

    FuzzFixture {
        verifier_creation_code,
        valid_calldata,
        proof_len: proof.len(),
        num_instance_cptr,
        proof_g1_ranges,
        eval_ranges,
        q_eval_ranges,
        instance_ranges: word_ranges(instance_cptr, public.len()),
    }
}

#[derive(Clone, Copy, Debug)]
struct RepackedLayout {
    prefix_g1: usize,
    num_evals: usize,
    num_point_sets: usize,
}

impl RepackedLayout {
    fn repacked_len(self) -> usize {
        self.prefix_g1 * G1_BYTES
            + self.num_evals * WORD_BYTES
            + G1_BYTES
            + self.num_point_sets * WORD_BYTES
            + G1_BYTES
    }
}

fn push_range(ranges: &mut Vec<Range<usize>>, start: usize, len: usize) {
    ranges.push(start..start + len);
}

fn word_ranges(start: usize, len: usize) -> Vec<Range<usize>> {
    (0..len)
        .map(|idx| {
            let start = start + idx * WORD_BYTES;
            start..start + WORD_BYTES
        })
        .collect()
}

fuzz_target!(|input: &[u8]| {
    if input.is_empty() {
        return;
    }

    let fixture = &*FIXTURE;
    let calldata = mutated_calldata(fixture, input);
    if calldata == fixture.valid_calldata {
        return;
    }

    let output = DEPLOYED.with(|deployed| deployed.borrow_mut().call(calldata));
    assert!(
        !output_is_true(output.as_deref()),
        "mutated Solidity verifier calldata returned true"
    );
});

fn mutated_calldata(fixture: &FuzzFixture, input: &[u8]) -> Vec<u8> {
    let mut calldata = fixture.valid_calldata.clone();
    match input[0] % 13 {
        0 => mutate_selector(&mut calldata, input),
        1 => mutate_abi_head(&mut calldata, PROOF_HEAD_CPTR, 0x40, input),
        2 => mutate_abi_head(
            &mut calldata,
            INSTANCES_HEAD_CPTR,
            0x40 + WORD_BYTES + fixture.proof_len,
            input,
        ),
        3 => mutate_abi_head(&mut calldata, PROOF_LEN_CPTR, fixture.proof_len, input),
        4 => mutate_one_range(&mut calldata, &fixture.proof_g1_ranges, input),
        5 => mutate_one_range(&mut calldata, &fixture.eval_ranges, input),
        6 => mutate_one_range(&mut calldata, &fixture.q_eval_ranges, input),
        7 => mutate_abi_head(&mut calldata, fixture.num_instance_cptr, 1, input),
        8 => mutate_one_range(&mut calldata, &fixture.instance_ranges, input),
        9 => append_trailing_bytes(&mut calldata, input),
        10 => truncate_calldata(&mut calldata, input),
        11 => insert_or_delete_near_proof(&mut calldata, fixture, input),
        _ => replace_with_raw_calldata(&mut calldata, input),
    }
    calldata
}

fn mutate_selector(calldata: &mut [u8], input: &[u8]) {
    let idx = pick(input, 1, FN_SIG_VERIFY_PROOF.len());
    calldata[idx] ^= nonzero_byte(input, 2);
}

fn mutate_abi_head(calldata: &mut [u8], offset: usize, valid: usize, input: &[u8]) {
    let value = match pick(input, 1, 8) {
        0 => 0,
        1 => valid.saturating_sub(WORD_BYTES),
        2 => valid + WORD_BYTES,
        3 => valid + pick(input, 2, 9) * WORD_BYTES,
        4 => SELECTOR_BYTES,
        5 => PROOF_CPTR,
        6 => usize::MAX,
        _ => return overwrite_word_from_input(calldata, offset, input, 2),
    };
    write_word_usize(calldata, offset, value);
    if read_word_usize(calldata, offset) == Some(valid) {
        calldata[offset + WORD_BYTES - 1] ^= 1;
    }
}

fn mutate_one_range(calldata: &mut [u8], ranges: &[Range<usize>], input: &[u8]) {
    if ranges.is_empty() {
        mutate_selector(calldata, input);
        return;
    }
    let range = &ranges[pick(input, 1, ranges.len())];
    let idx = range.start + pick(input, 2, range.len());
    calldata[idx] ^= nonzero_byte(input, 3);
}

fn append_trailing_bytes(calldata: &mut Vec<u8>, input: &[u8]) {
    let len = 1 + pick(input, 1, 256);
    for idx in 0..len {
        calldata.push(input.get(2 + idx).copied().unwrap_or(idx as u8));
    }
}

fn truncate_calldata(calldata: &mut Vec<u8>, input: &[u8]) {
    if calldata.is_empty() {
        return;
    }
    let len = pick(input, 1, calldata.len());
    calldata.truncate(len);
}

fn insert_or_delete_near_proof(calldata: &mut Vec<u8>, fixture: &FuzzFixture, input: &[u8]) {
    let positions = [
        PROOF_LEN_CPTR,
        PROOF_CPTR,
        PROOF_CPTR + pick(input, 2, fixture.proof_len.max(1)),
        fixture.num_instance_cptr,
    ];
    let pos = positions[pick(input, 1, positions.len())].min(calldata.len());
    let len = WORD_BYTES.min(calldata.len().saturating_sub(pos)).max(1);
    if pick(input, 3, 2) == 0 && calldata.len() + WORD_BYTES <= MAX_RAW_CALLDATA {
        calldata.splice(pos..pos, [0u8; WORD_BYTES]);
    } else {
        calldata.drain(pos..pos + len);
    }
}

fn replace_with_raw_calldata(calldata: &mut Vec<u8>, input: &[u8]) {
    let raw = input.get(1..).unwrap_or_default();
    let len = raw.len().min(MAX_RAW_CALLDATA);
    calldata.clear();
    calldata.extend_from_slice(&raw[..len]);
}

fn overwrite_word_from_input(
    calldata: &mut [u8],
    offset: usize,
    input: &[u8],
    input_offset: usize,
) {
    if offset + WORD_BYTES > calldata.len() {
        return;
    }
    for idx in 0..WORD_BYTES {
        calldata[offset + idx] = input.get(input_offset + idx).copied().unwrap_or(idx as u8);
    }
}

fn write_word_usize(calldata: &mut [u8], offset: usize, value: usize) {
    if offset + WORD_BYTES > calldata.len() {
        return;
    }
    calldata[offset..offset + WORD_BYTES].fill(0);
    let bytes = value.to_be_bytes();
    calldata[offset + WORD_BYTES - bytes.len()..offset + WORD_BYTES].copy_from_slice(&bytes);
}

fn read_word_usize(calldata: &[u8], offset: usize) -> Option<usize> {
    if offset + WORD_BYTES > calldata.len() {
        return None;
    }
    let mut bytes = [0u8; std::mem::size_of::<usize>()];
    let source = &calldata[offset + WORD_BYTES - bytes.len()..offset + WORD_BYTES];
    bytes.copy_from_slice(source);
    Some(usize::from_be_bytes(bytes))
}

fn output_is_true(output: Option<&[u8]>) -> bool {
    let Some(output) = output else {
        return false;
    };
    output.len() == WORD_BYTES
        && output[..WORD_BYTES - 1].iter().all(|byte| *byte == 0)
        && output[WORD_BYTES - 1] == 1
}

fn pick(input: &[u8], offset: usize, modulo: usize) -> usize {
    if modulo == 0 {
        return 0;
    }
    usize::from(input.get(offset).copied().unwrap_or(0)) % modulo
}

fn nonzero_byte(input: &[u8], offset: usize) -> u8 {
    input.get(offset).copied().unwrap_or(1) | 1
}
