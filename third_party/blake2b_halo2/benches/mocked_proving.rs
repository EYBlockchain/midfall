use criterion::{
    criterion_group, criterion_main, BatchSize, BenchmarkGroup, BenchmarkId, Criterion, Throughput,
};
use criterion::measurement::WallTime;
use blake2b_halo2::usage_utils::circuit_runner::CircuitRunner;

pub mod utils;
use utils::*;

criterion_group!(mocked_prover, benchmark_mocked_proving);
criterion_main!(mocked_prover);

pub fn benchmark_mocked_proving(c: &mut Criterion) {
    let mut group = c.benchmark_group("optimization_comparison");
    configure_group(&mut group);

    for amount_of_blocks in benchmarking_block_sizes() {
        group.throughput(Throughput::Bytes(amount_of_blocks as u64));

        benchmark_optimization_with_amount_of_blocks(&mut group, amount_of_blocks, "opt_recycle");
    }
    group.finish()
}

fn benchmark_optimization_with_amount_of_blocks(
    group: &mut BenchmarkGroup<WallTime>,
    amount_of_blocks: usize,
    optimization_name: &str,
) {
    group.bench_function(BenchmarkId::new(optimization_name, amount_of_blocks), |b| {
        b.iter_batched(
            || {
                let ci = random_input_for_desired_blocks(amount_of_blocks);
                let circuit = CircuitRunner::create_circuit_for_packed_inputs(ci.clone());
                (circuit, ci.4)
            },
            |(circuit, expected)| {
                CircuitRunner::mock_prove_with_public_inputs_ref(&expected, &circuit)
            },
            BatchSize::SmallInput,
        )
    });
}
