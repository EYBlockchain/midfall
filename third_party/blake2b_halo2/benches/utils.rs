use criterion::{BenchmarkGroup, SamplingMode};
use criterion::measurement::WallTime;
use midnight_proofs::circuit::Value;
use midnight_curves::bls12_381::Fq;
use rand::Rng;
use blake2b_halo2::usage_utils::circuit_runner::Blake2bCircuitInputs;
use blake2_rfc::blake2b::blake2b;

pub fn benchmarking_block_sizes() -> Vec<usize> {
    vec![1, 5, 10, 20, 30]
}

pub fn sample_size() -> usize {
    30
}

pub fn configure_group(group: &mut BenchmarkGroup<WallTime>) {
    group.sampling_mode(SamplingMode::Flat);
    group.sample_size(sample_size());
    //group.measurement_time(Duration::from_secs(1000));
}

pub fn random_input_for_desired_blocks(amount_of_blocks: usize) -> Blake2bCircuitInputs {
    let mut rng = rand::thread_rng();

    let input_size = amount_of_blocks * 128;
    const OUTPUT_SIZE: usize = 64;
    let random_input_bytes: Vec<u8> = (0..input_size).map(|_| rng.gen_range(0..=255)).collect();
    let random_inputs: &str = &hex::encode(&random_input_bytes);
    let key: &str = "";
    let output_size = OUTPUT_SIZE;

    let hash_result = run_blake2b(random_inputs, key, output_size);

    let expected_output_: Vec<Fq> = hash_result.iter().map(|byte| Fq::from(*byte as u64)).collect();
    let expected_output: [Fq; OUTPUT_SIZE] = expected_output_.try_into().unwrap();
    let input_values: Vec<Value<Fq>> =
        random_input_bytes.iter().map(|x| Value::known(Fq::from(*x as u64))).collect();
    let key_size = 0;
    let key_values: Vec<Value<Fq>> = vec![];

    (input_values, input_size, key_values, key_size, expected_output, OUTPUT_SIZE)
}

fn run_blake2b(input: &str, key: &str, output_size: usize) -> Vec<u8> {
    let res = blake2b(output_size, key.as_bytes(), input.as_bytes());
    res.as_bytes().into()
}
