//! Phase 2 unit test: IVC final-step Keccak round-trip.
//!
//! Builds a 1-step IVC chain over a trivial Poseidon-hash transition
//! (minimum overhead: 1 Poseidon iter per step), proves the final step
//! under a Keccak-256 transcript via `IvcProver::prove_final_step`,
//! and verifies the resulting proof off-circuit via
//! `IvcVerifier::verify_final`.
//!
//! Gated `#[ignore]` because IVC at the smallest viable k (~18) still
//! takes several minutes to prove on a typical laptop. Requires the
//! Filecoin SRS at $SRS_DIR/bls_filecoin_2p<k> (defaults to
//! `./examples/assets`, which is checked into the aggregation crate).
//!
//! Run with:
//!   cargo test --test ivc_keccak_final \
//!     --features keccak-transcript,truncated-challenges \
//!     -- --ignored --nocapture

#![cfg(feature = "keccak-transcript")]

use ff::Field;
use midnight_aggregation::ivc::{self, IvcCircuit, IvcContext, IvcIO, IvcState, IvcTransition};
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, *},
    types::AssignedNative,
    verifier::{BlstrsEmulation, SelfEmulation},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{
    utils::plonk_api::{load_srs, SrsSource},
    ZkStdLib, ZkStdLibArch,
};

type S = BlstrsEmulation;
type F = <S as SelfEmulation>::F;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct State {
    cnt: F,
    val: F,
}

#[derive(Clone, Debug)]
struct AssignedState {
    cnt: AssignedNative<F>,
    val: AssignedNative<F>,
}

/// Trivial IVC transition: hash `val` with Poseidon once and bump `cnt`.
#[derive(Clone, Debug)]
struct PoseidonChain {
    std_lib: ZkStdLib,
}

impl IvcContext for PoseidonChain {
    type Context = ();
    fn new(std_lib: ZkStdLib, _ctx: &()) -> Self {
        PoseidonChain { std_lib }
    }
    fn write_context<W: std::io::Write>(_ctx: &(), _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }
    fn read_context<R: std::io::Read>(_reader: &mut R) -> std::io::Result<()> {
        Ok(())
    }
}

impl IvcState for PoseidonChain {
    type State = State;
    type AssignedState = AssignedState;

    fn genesis(_ctx: &()) -> Self::State {
        State {
            cnt: F::ZERO,
            val: F::ZERO,
        }
    }

    fn decider(_ctx: &Self::Context, _state: &Self::State) -> bool {
        true
    }
}

impl IvcIO for PoseidonChain {
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<State>,
    ) -> Result<AssignedState, Error> {
        let scalar_chip = self.std_lib.bls12_381_scalar();
        Ok(AssignedState {
            cnt: scalar_chip.assign(layouter, value.as_ref().map(|s| s.cnt))?,
            val: scalar_chip.assign(layouter, value.as_ref().map(|s| s.val))?,
        })
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<(), Error> {
        let scalar_chip = self.std_lib.bls12_381_scalar();
        scalar_chip.constrain_as_public_input(layouter, &state.cnt)?;
        scalar_chip.constrain_as_public_input(layouter, &state.val)
    }

    fn as_public_input(
        &self,
        _layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok(vec![state.cnt.clone(), state.val.clone()])
    }

    fn format_public_input(state: &State) -> Vec<F> {
        vec![state.cnt, state.val]
    }
}

impl IvcTransition for PoseidonChain {
    type Witness = ();

    fn arch() -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn transition(_ctx: &(), state: &Self::State, _witness: Self::Witness) -> Self::State {
        State {
            cnt: state.cnt + F::ONE,
            val: <PoseidonChip<F> as HashCPU<F, F>>::hash(&[state.val]),
        }
    }

    fn circuit_transition(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
        _witness: Value<Self::Witness>,
    ) -> Result<Self::AssignedState, Error> {
        let scalar_chip = self.std_lib.bls12_381_scalar();
        let val = self.std_lib.poseidon(layouter, std::slice::from_ref(&state.val))?;
        let cnt = scalar_chip.add_constant(layouter, &state.cnt, F::ONE)?;
        Ok(AssignedState { cnt, val })
    }
}

/// Drives a 1-step IVC chain whose final proof uses a Keccak transcript,
/// then off-circuit-verifies the final proof via `verify_final`.
#[test]
#[ignore = "slow IVC proving (~minutes); run with --ignored --features keccak-transcript,truncated-challenges"]
fn ivc_keccak_final_round_trip() {
    use std::time::Instant;
    const K: u32 = 18;

    let srs = load_srs(SrsSource::Filecoin, K, IvcCircuit::<PoseidonChain>::cs_degree());

    let setup_t = Instant::now();
    let (mut prover, verifier) = ivc::setup::<PoseidonChain>(srs, K, ());
    println!("[ivc-keccak] setup completed in {:.2?}", setup_t.elapsed());

    let prove_t = Instant::now();
    let proof = prover
        .prove_final_step(())
        .expect("prove_final_step should succeed at genesis");
    println!(
        "[ivc-keccak] prove_final_step completed in {:.2?} ({} bytes)",
        prove_t.elapsed(),
        proof.len()
    );

    let instance = prover.instance();

    // Native verify_final must accept the prove_final_step output.
    let verify_t = Instant::now();
    verifier
        .verify_final::<PoseidonChain>(&(), &instance, &proof)
        .expect("verify_final should accept a prove_final_step output");
    println!("[ivc-keccak] verify_final completed in {:.2?}", verify_t.elapsed());

    // Cross-check: regular verify (Poseidon transcript) must REJECT a
    // Keccak-transcript proof. This guards against accidental fall-back
    // to the wrong transcript.
    let crossed = verifier.verify::<PoseidonChain>(&(), &instance, &proof);
    assert!(
        crossed.is_err(),
        "Poseidon-transcript verify must NOT accept a Keccak-transcript proof"
    );
    println!("[ivc-keccak] cross-transcript rejection: OK");

    println!("[ivc-keccak] PASS");
}
