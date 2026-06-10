use blake2b_halo2::usage_utils::circuit_runner::CircuitRunner;
use criterion::measurement::WallTime;
use criterion::{
    criterion_group, criterion_main, BatchSize, BenchmarkGroup, BenchmarkId, Criterion, Throughput,
};
use midnight_curves::bls12_381::Bls12;
use midnight_proofs::poly::kzg::params::ParamsKZG;

pub mod utils;
use utils::*;

criterion_group!(vk, benchmark_verification_key_generation);
criterion_main!(vk);

pub fn benchmark_verification_key_generation(c: &mut Criterion) {
    let mut group = c.benchmark_group("verification_key");
    configure_group(&mut group);

    let params = ParamsKZG::<Bls12>::unsafe_setup(17, &mut rand::thread_rng());

    for amount_of_blocks in benchmarking_block_sizes() {
        group.throughput(Throughput::Bytes(amount_of_blocks as u64));

        benchmark_verification_key(&params, &mut group, amount_of_blocks, "opt_recycle");
    }
    group.finish()
}

fn benchmark_verification_key(
    params: &ParamsKZG<Bls12>,
    group: &mut BenchmarkGroup<WallTime>,
    amount_of_blocks: usize,
    name: &str,
) {
    group.bench_function(BenchmarkId::new(name, amount_of_blocks), |b| {
        b.iter_batched(
            || {
                let ci = random_input_for_desired_blocks(amount_of_blocks);
                CircuitRunner::create_circuit_for_packed_inputs(ci.clone())
            },
            |circuit| CircuitRunner::create_vk(&circuit, params),
            BatchSize::SmallInput,
        )
    });
}
