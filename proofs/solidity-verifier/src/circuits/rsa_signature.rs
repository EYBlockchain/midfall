//! Helpers to produce an RSA-signature proof + verifying key matching
//! `zk_stdlib/examples/rsa_signature.rs`.
//!
//! Given an RSA public key `(e, m)` and a message `msg` as public
//! inputs, this relation proves knowledge of an integer `s` such that
//! `s^e = msg (mod m)` with `e = 3` and `m` a 1024-bit modulus.
//!
//! Unlike the poseidon example, the RSA circuit exercises several
//! features the current `contracts/PoseidonVerifier.sol` does NOT yet
//! support (see ARCHITECTURE.md §7.2 and §9):
//!
//!   * Multiple lookups (pow2range + biguint chips).
//!   * Multi-value instance columns (1024-bit pk + 1024-bit msg each
//!     decomposed into many Fq limbs via `AssignedBigUint`).
//!   * Non-trivial `fixed_queries` / per-phase challenges shape.
//!
//! Phase 1 materialises the VK contract + proof fixtures for this
//! circuit so the Phase 2+ generalisation work has concrete on-disk
//! targets to validate against; running `verify()` on the produced
//! proof today trips `require(vk.numLookups == 1)` inside the
//! verifier contract.

use std::ops::Rem;

use midnight_circuits::{biguint::AssignedBigUint, instructions::AssertionInstructions};
use midnight_curves::Fq;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::kzg::params::ParamsKZG,
};
use midnight_zk_stdlib::{
    utils::plonk_api::srs_for_test, MidnightPK, MidnightVK, Relation, ZkStdLib,
    ZkStdLibArch,
};
use num_bigint::{BigUint, RandBigInt};
use num_traits::{Num, One};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use sha3::Keccak256;

/// RSA public exponent (matches `zk_stdlib/examples/rsa_signature.rs`).
pub const E: u64 = 3;

/// 1024-bit modulus / message width (matches the zk_stdlib example).
pub const NB_BITS: u32 = 1024;

/// Replica of the example circuit from
/// `zk_stdlib/examples/rsa_signature.rs`.
#[derive(Clone, Default)]
pub struct RsaSignatureExample;

pub type Modulus = BigUint;
pub type Message = BigUint;
pub type Signature = BigUint;
pub type PK = Modulus;

impl Relation for RsaSignatureExample {
    type Instance = (PK, Message);
    type Witness = Signature;

    fn format_instance((pk, msg): &Self::Instance) -> Result<Vec<Fq>, Error> {
        Ok([
            AssignedBigUint::<Fq>::as_public_input(pk, NB_BITS),
            AssignedBigUint::<Fq>::as_public_input(msg, NB_BITS),
        ]
        .into_iter()
        .flatten()
        .collect())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<Fq>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let biguint = std_lib.biguint();

        let public_key = biguint.assign_biguint(
            layouter,
            instance.as_ref().map(|(pk, _)| pk.clone()),
            NB_BITS,
        )?;
        let message =
            biguint.assign_biguint(layouter, instance.map(|(_, msg)| msg), NB_BITS)?;
        let signature = biguint.assign_biguint(layouter, witness, NB_BITS)?;

        biguint.constrain_as_public_input(layouter, &public_key, NB_BITS)?;
        biguint.constrain_as_public_input(layouter, &message, NB_BITS)?;

        let expected_msg = biguint.mod_exp(layouter, &signature, E, &public_key)?;
        biguint.assert_equal(layouter, &message, &expected_msg)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(
        &self,
        _writer: &mut W,
    ) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(RsaSignatureExample)
    }
}

/// Hardcoded 512-bit primes producing a deterministic 1024-bit RSA
/// modulus. Matches `zk_stdlib/examples/rsa_signature.rs`.
fn demo_primes() -> (BigUint, BigUint) {
    let p = BigUint::from_str_radix(
        "81e05798232330a8c7059621c812dc9d2bba37edbd0e79f101eef1db373c12724595480ae6a9dbbf158fa65d6910b8aea7b3be2eede9123ede8d84ec9e8ee907",
        16,
    )
    .expect("p parses");
    let q = BigUint::from_str_radix(
        "acd6fd3c0d70502e8ecefb20259fbf4783a614a0fb1a33701e3adc84947326a754f8a632e5f6cd718a681cde953024b3612bb0646f180b6fd063b1ef4e10d4a5",
        16,
    )
    .expect("q parses");
    (p, q)
}

pub struct RsaSignatureFixture {
    pub srs: ParamsKZG<midnight_curves::Bls12>,
    pub vk: MidnightVK,
    pub pk: MidnightPK<RsaSignatureExample>,
    pub relation: RsaSignatureExample,
    pub instance: (BigUint, BigUint),
    pub witness: BigUint,
    pub proof: Vec<u8>,
}

impl RsaSignatureFixture {
    /// Build (setup + prove) a single RSA-signature proof using the
    /// Keccak256 Fiat-Shamir transcript.
    ///
    /// `k` defaults to 12 when callers use `k=0`, matching the
    /// zk_stdlib example. The message is drawn from a seeded
    /// `ChaCha8Rng`, so the `(instance, witness)` pair is deterministic
    /// for a given `(k, seed)`. Proof bytes are *not* bit-reproducible
    /// because `midnight-proofs`' prover also pulls blinding values
    /// from the runtime `OsRng`.
    pub fn build(k: u32, seed: u64) -> Self {
        let relation = RsaSignatureExample;
        let srs = srs_for_test(&relation, Some(k));
        let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
        let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

        let (p, q) = demo_primes();
        let phi = (&p - BigUint::one()) * (&q - BigUint::one());
        let d = BigUint::from(E).modinv(&phi).expect("phi coprime with e");
        let public_key = &p * &q;

        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let message = rng.gen_biguint(NB_BITS as u64).rem(&public_key);
        let signature = message.modpow(&d, &public_key);

        let instance = (public_key.clone(), message.clone());

        let prover_rng = ChaCha8Rng::seed_from_u64(seed.wrapping_add(1));
        let proof = midnight_zk_stdlib::prove::<RsaSignatureExample, Keccak256>(
            &srs,
            &pk,
            &relation,
            &instance,
            signature.clone(),
            prover_rng,
        )
        .expect("RSA proof generation should not fail");

        Self {
            srs,
            vk,
            pk,
            relation,
            instance,
            witness: signature,
            proof,
        }
    }
}
