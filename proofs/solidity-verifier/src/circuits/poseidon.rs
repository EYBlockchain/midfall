//! Helpers to produce a poseidon proof + verifying key matching
//! `zk_stdlib/examples/poseidon.rs`.

use ff::Field;
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
};
use midnight_curves::Fq;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use sha3::Keccak256;

/// Replica of the example circuit from `zk_stdlib/examples/poseidon.rs`.
#[derive(Clone, Default)]
pub struct PoseidonExample;

impl Relation for PoseidonExample {
    type Instance = Fq;

    type Witness = [Fq; 3];

    fn format_instance(instance: &Self::Instance) -> Result<Vec<Fq>, Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<Fq>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned_message = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.poseidon(layouter, &assigned_message)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonExample)
    }
}

pub struct PoseidonFixture {
    pub srs: midnight_proofs::poly::kzg::params::ParamsKZG<midnight_curves::Bls12>,
    pub vk: midnight_zk_stdlib::MidnightVK,
    pub pk: midnight_zk_stdlib::MidnightPK<PoseidonExample>,
    pub relation: PoseidonExample,
    pub instance: Fq,
    pub witness: [Fq; 3],
    pub proof: Vec<u8>,
}

impl PoseidonFixture {
    /// Build (setup + prove) a single poseidon proof using Keccak256 transcript.
    ///
    /// `k` defaults to 6 (64 rows), matching `zk_stdlib/examples/poseidon.rs`.
    pub fn build(k: u32, seed: u64) -> Self {
        let relation = PoseidonExample;
        let srs = srs_for_test(&relation, Some(k));
        let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
        let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let witness: [Fq; 3] = core::array::from_fn(|_| Fq::random(&mut rng));
        let instance = <PoseidonChip<Fq> as HashCPU<Fq, Fq>>::hash(&witness);

        // Prover rng is seeded deterministically too so the proof bytes are
        // byte-for-byte reproducible for the equivalence test.
        let prover_rng = ChaCha8Rng::seed_from_u64(seed.wrapping_add(1));
        let proof = midnight_zk_stdlib::prove::<PoseidonExample, Keccak256>(
            &srs, &pk, &relation, &instance, witness, prover_rng,
        )
        .expect("Proof generation should not fail");

        Self { srs, vk, pk, relation, instance, witness, proof }
    }
}
