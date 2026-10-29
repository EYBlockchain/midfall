//! P-FREEZE / F-3: the regeneration harness for the frozen poseidon fixture set
//! (`proofs/solidity-verifier/fixtures/poseidon/`), re-landed after P-M0 ran it
//! once as a scratch file (D-P28, `formal/BASELINE.md` "Generator status") and
//! deleted it. Until this file existed, nothing in the tree could re-emit those
//! six artefacts - the recipe was prose.
//!
//! **ENV-GATED AND INERT BY DEFAULT - READ THIS BEFORE "FIXING" IT.**
//! Every test here returns immediately unless its own output variable is set:
//!
//! * `m0_regen_poseidon_fixtures` does nothing unless `M0_OUT` names a scratch
//!   directory, and additionally requires `HALO2_SOLIDITY_RUN_EVM_TESTS=1`.
//! * `m0_replay_directory` does nothing unless `M0_REPLAY_DIR` names a fixture
//!   directory.
//!
//! The gate is not decoration. Ungated, these tests fail on any host without the
//! Filecoin `bls_filecoin_2p6` asset or the pinned solc, and would add noise to
//! `cargo test --all-targets` - which is *already* red on 39 unrelated tests
//! (missing extended-domain SRS assets under `outer-single-h-commitment`; see the
//! G0 table in `formal/BASELINE.md`). Keep this file silent under a plain
//! `--all-targets` run.
//!
//! **THE ASSERTIONS ARE STRUCTURAL, NOT BYTEWISE - DO NOT "FIX" THAT.**
//! `proof.bin` is a *recorded accepted run*, not a reproducible build:
//! `blind_quotient_limbs` (`proofs/src/plonk/prover.rs:126`, the
//! `cfg(not(feature = "single-h-commitment"))` variant) draws its blinding scalars
//! from `OsRng`, which ignores every seed this harness passes. Two runs with
//! identical seeds agree for the first 720 bytes (the 15 pre-quotient point reads)
//! and diverge from byte 721 on. Both runs verify. So this harness asserts the
//! *shape* - 2,640 bytes, 21 point reads + 51 scalar reads = 72 transcript reads,
//! and a real ACCEPT from the native verifier and from the generated Solidity
//! verifier on both quotient lowerings - and never compares proof bytes to the
//! committed file. Anyone who replaces that with
//! `assert_eq!(proof, fs::read("proof.bin"))` builds a test that flakes on every
//! run. The per-artefact byte comparison this harness does print is a report, not
//! an assertion; see `report_against_committed`.
//!
//! Recorded profile, reproduced exactly (same circuit path as
//! `tests/poseidon_fixture.rs`; `formal/BASELINE.md` "Poseidon fixture
//! regeneration (D-P28)"):
//!
//! | item | value |
//! |---|---|
//! | cargo features | `evm,rust-verifier-trace` on `halo2_solidity_verifier` - implies `truncated-challenges` and `midnight-proofs/solidity-verifier-trace`; `outer-fewer-point-sets` and `outer-single-h-commitment` NOT set, i.e. `outerFewerPointSets = false` |
//! | cargo profile | `--release` |
//! | circuit | `PoseidonExample` at `k = 6` |
//! | witness RNG | `ChaCha8Rng::seed_from_u64(42)` |
//! | prover RNG | `ChaCha8Rng::seed_from_u64(0xdebd)` |
//! | SRS | `zk_stdlib/examples/assets/bls_filecoin_2p6` via `srs_for_test(_, Some(6))` |
//! | solc | pinned `0.8.30+commit.73712a01` (`proofs/solidity-verifier/.solc/solc`) |
//! | revm | 19, Prague handler (EIP-2537 G1ADD / G1MSM / PAIRING) |
//!
//! Regenerate the six artefacts into a scratch directory like this (`cargo` comes
//! from `$HOME/.rustup/toolchains/1.90.0-aarch64-apple-darwin/bin`):
//!
//! ```text
//! export SOLC="$PWD/proofs/solidity-verifier/.solc/solc"   # the pinned 0.8.30
//! export HALO2_SOLIDITY_RUN_EVM_TESTS=1 M0_OUT=/tmp/m0-regen
//! cargo test --release -p halo2_solidity_verifier \
//!   --features evm,rust-verifier-trace --test m0_poseidon_regen -- --nocapture
//! ```
//!
//! It writes only into `M0_OUT`. It never touches `fixtures/poseidon/`, the
//! `target/*-fixture-dump/` directories the Lean render gates read, or
//! `formal/fixtures/conformance/`.

#![cfg(all(feature = "evm", feature = "rust-verifier-trace"))]

use std::{
    collections::BTreeMap,
    env,
    fs::{self, File},
    io::{BufWriter, Write},
    path::{Path, PathBuf},
};

use ff::{Field, PrimeField};
use halo2_solidity_verifier::{
    compile_solidity, pinned_solc_available, CallOutcome, Evm, GeneratorConfig, QuotientLowering,
    RenderDiagnostics, RenderOptions, RenderVk, SolidityGenerator,
};
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
};
use midnight_curves::Fq;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{
        solidity_trace::{self, SolidityTraceEvent},
        Error,
    },
    transcript::Hashable,
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{
    utils::plonk_api::srs_for_test, MidnightVK, Relation, ZkStdLib, ZkStdLibArch,
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use serde_json::{json, Map, Value as Json};
use sha3::Keccak256;

type F = Fq;

/// The frozen circuit's domain size.
const K: u32 = 6;
/// Witness RNG seed recorded by D-P28.
const WITNESS_SEED: u64 = 42;
/// Prover RNG seed recorded by D-P28.
const PROVER_RNG_SEED: u64 = 0xdebd;
/// `PoseidonExample` formats exactly one public input.
const NUM_INSTANCES: usize = 1;
/// ZkStdLib creates two instance columns, one of them committed.
const NUM_COMMITTED_INSTANCES: usize = 1;

/// Recorded proof length in bytes: 21 * 48 + 51 * 32.
const EXPECTED_PROOF_LEN: usize = 2_640;
/// Compressed G1 reads in the recorded proof stream.
const EXPECTED_POINT_READS: usize = 21;
/// Scalar reads in the recorded proof stream.
const EXPECTED_SCALAR_READS: usize = 51;
/// Total transcript reads: EXPECTED_POINT_READS + EXPECTED_SCALAR_READS.
const EXPECTED_TRANSCRIPT_READS: usize = EXPECTED_POINT_READS + EXPECTED_SCALAR_READS; // 72
/// How many leading bytes two runs agree on before OsRng quotient-limb blinding
/// takes over. Reported, never asserted (see the module comment).
const PRE_BLINDING_PREFIX_BYTES: usize = 720;

const RUN_EVM_TESTS_ENV: &str = "HALO2_SOLIDITY_RUN_EVM_TESTS";
const OUT_ENV: &str = "M0_OUT";
const REPLAY_DIR_ENV: &str = "M0_REPLAY_DIR";
const REPLAY_EXPECT_ENV: &str = "M0_EXPECT";

/// The six artefacts `formal/BASELINE.md` pins under `fixtures/poseidon/`.
const FIXTURE_ARTEFACTS: [&str; 6] = [
    "proof.bin",
    "vk.bin",
    "instance.be",
    "rust_trace.json",
    "solidity_trace.json",
    "verifier_trace.bin",
];

#[derive(Clone, Default)]
struct PoseidonExample;

impl Relation for PoseidonExample {
    type Instance = F;
    type Witness = [F; 3];

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

/// The recorded run: SRS, VK, instance, proof, and the native trace of the
/// verifier run that accepted it.
struct Regenerated {
    srs: midnight_proofs::poly::kzg::params::ParamsKZG<midnight_curves::Bls12>,
    vk: MidnightVK,
    instance: F,
    proof: Vec<u8>,
    native_events: Vec<SolidityTraceEvent>,
    point_reads: usize,
    scalar_reads: usize,
}

/// Prove the recorded circuit under the recorded profile and check the proof
/// really verifies natively, with the solidity_trace hooks on so the native trace
/// is re-emitted from the run that accepted.
fn regenerate() -> Regenerated {
    let srs_dir = env::var("SRS_DIR").unwrap_or_else(|_| {
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../zk_stdlib/examples/assets"
        )
        .to_string()
    });
    let srs_path = format!("{srs_dir}/bls_filecoin_2p{K}");
    assert!(
        Path::new(&srs_path).exists(),
        "{OUT_ENV} is set but the recorded SRS asset is missing at {srs_path}; fetch it \
         (scripts/ensure_srs_assets.sh) or unset {OUT_ENV}"
    );
    env::set_var("SRS_DIR", &srs_dir);

    let relation = PoseidonExample;
    let srs = srs_for_test(&relation, Some(K));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
    let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);

    let mut rng = ChaCha8Rng::seed_from_u64(WITNESS_SEED);
    let witness: [F; 3] = core::array::from_fn(|_| F::random(&mut rng));
    let instance = <PoseidonChip<F> as HashCPU<F, F>>::hash(&witness);

    let prover_rng = ChaCha8Rng::seed_from_u64(PROVER_RNG_SEED);
    let proof = midnight_zk_stdlib::prove::<PoseidonExample, Keccak256>(
        &srs, &pk, &relation, &instance, witness, prover_rng,
    )
    .expect("poseidon proof generation must succeed");

    // ---- STRUCTURAL assertions, never a byte comparison against the committed
    //      proof: OsRng quotient-limb blinding makes the tail unrepeatable. ----
    assert_eq!(
        proof.len(),
        EXPECTED_PROOF_LEN,
        "regen: the recorded profile must produce the {}-byte proof (21 x 48 + 51 x 32); a \
         different length means the feature profile moved, not that the fixture is stale",
        EXPECTED_PROOF_LEN
    );

    // The accepted native run, traced. verify drives prepare, which is where the
    // solidity_trace hooks live, so the trace is a by-product of the run that
    // actually accepted - not a reconstruction. (docs/REVIEW.md R-56 correction:
    // the deleted trace_replay.rs was exactly a reconstruction.)
    solidity_trace::start();
    let verdict = midnight_zk_stdlib::verify::<PoseidonExample, Keccak256>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof,
    );
    let native_events = solidity_trace::take();
    verdict.expect("the native verifier must accept the regenerated proof");

    let point_reads = native_events.iter().filter(|e| (10_000..20_000).contains(&e.id)).count();
    let scalar_reads = native_events.iter().filter(|e| (20_000..30_000).contains(&e.id)).count();
    assert_eq!(
        point_reads, EXPECTED_POINT_READS,
        "regen: expected {EXPECTED_POINT_READS} compressed-G1 transcript reads"
    );
    assert_eq!(
        scalar_reads, EXPECTED_SCALAR_READS,
        "regen: expected {EXPECTED_SCALAR_READS} scalar transcript reads"
    );
    assert_eq!(
        point_reads + scalar_reads,
        EXPECTED_TRANSCRIPT_READS,
        "regen: the recorded proof is {EXPECTED_TRANSCRIPT_READS} transcript reads"
    );
    assert_eq!(
        point_reads * 48 + scalar_reads * 32,
        proof.len(),
        "regen: the proof length must be exactly the transcript reads it is made of"
    );

    Regenerated {
        srs,
        vk,
        instance,
        proof,
        native_events,
        point_reads,
        scalar_reads,
    }
}

/// Render, compile, deploy and call the generated verifier; return its gas and LOG
/// stream. Acceptance is asserted here: this is the leg that proves the
/// regenerated proof passes the *Solidity* verifier, not only the Rust one.
fn verify_on_evm(
    label: &str,
    generator: &SolidityGenerator<'_>,
    run: &Regenerated,
    lowering: QuotientLowering,
    traced: bool,
) -> (u64, Vec<halo2_solidity_verifier::revm::primitives::Log>) {
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            quotient_lowering: lowering,
            diagnostics: RenderDiagnostics {
                trace: traced,
                ..RenderDiagnostics::default()
            },
            ..RenderOptions::default()
        })
        .expect("render should succeed");
    let verifier_solidity = artifacts.verifier;
    let vk_solidity = artifacts.verifying_key.expect("separate render includes VK");
    if traced {
        let dir = out_dir().expect("M0_OUT");
        fs::write(dir.join("Halo2Verifier.traced.sol"), &verifier_solidity)
            .expect("write the traced verifier source");
        fs::write(dir.join("Halo2VerifyingKey.traced.sol"), &vk_solidity)
            .expect("write the traced VK source");
    }

    let mut evm = Evm::default();
    let vk_address = evm.create(compile_solidity(&vk_solidity));
    let verifier_address =
        evm.create_with_address_arg(compile_solidity(&verifier_solidity), vk_address);
    let calldata = generator
        .encode_calldata(&run.proof, &[run.instance])
        .expect("the generated verifier must encode this proof as calldata");

    let (gas_used, logs) = match evm.try_call_with_gas(verifier_address, calldata, 5_000_000_000) {
        CallOutcome::Success {
            gas_used,
            output,
            logs,
        } => {
            assert_eq!(
                output,
                [vec![0u8; 31], vec![1]].concat(),
                "{label} verifier must ACCEPT the regenerated proof (gas_used = {gas_used}, \
                 output = 0x{})",
                hex::encode(&output)
            );
            (gas_used, logs)
        }
        CallOutcome::Revert { gas_used, output } => panic!(
            "{label} verifier REVERTED the regenerated proof, gas_used = {gas_used}, \
             output = 0x{}",
            hex::encode(&output)
        ),
        CallOutcome::Halt { gas_used, reason } => panic!(
            "{label} verifier HALTED on the regenerated proof, gas_used = {gas_used}, \
             reason = {reason}"
        ),
    };
    eprintln!("[m0-regen] {label} solidity ACCEPT ({gas_used} gas)");
    (gas_used, logs)
}

// ---------------------------------------------------------------------------
// Container writers. These reproduce the containers the committed artefacts use,
// as documented in formal/BASELINE.md "Container notes".
// ---------------------------------------------------------------------------

/// Trace ids 1..=36 of the generated Yul tracer, plus the per-range bases.
fn yul_trace_name(id: u64) -> (String, &'static str) {
    const FIXED: [(u64, &str); 36] = [
        (1, "vk_digest"),
        (2, "num_instances"),
        (3, "k"),
        (4, "n_inv"),
        (5, "omega"),
        (6, "omega_inv"),
        (7, "theta"),
        (8, "beta"),
        (9, "gamma"),
        (10, "y"),
        (11, "x"),
        (12, "trash_challenge"),
        (13, "x1"),
        (14, "x2"),
        (15, "x3"),
        (16, "x4"),
        (17, "x_n"),
        (18, "x_n_minus_1_inv"),
        (19, "l_last"),
        (20, "l_blind"),
        (21, "l_0"),
        (22, "instance_eval"),
        (23, "linearization_expected_eval"),
        (24, "quotient"),
        (25, "f_com"),
        (26, "pi"),
        (27, "pairing_lhs"),
        (28, "pairing_rhs"),
        (29, "acc_lhs"),
        (30, "acc_rhs"),
        (31, "f_eval"),
        (32, "v"),
        (33, "final_com"),
        (34, "linearization_commitment"),
        (35, "final_result"),
        (36, "quotient_numerator"),
    ];
    let indexed = |base: u64, prefix: &str| format!("{prefix}[{}]", id - base);
    if let Some((_, name)) = FIXED.iter().find(|(i, _)| *i == id) {
        let kind = if (7..=16).contains(&id) {
            "Challenge"
        } else {
            "Intermediate"
        };
        return (name.to_string(), kind);
    }
    if (1_000..2_000).contains(&id) {
        return (indexed(1_000, "user_challenge"), "Challenge");
    }
    if (10_000..20_000).contains(&id) {
        return (indexed(10_000, "proof_commitment"), "ReadPoint");
    }
    if (20_000..30_000).contains(&id) {
        return (indexed(20_000, "proof_eval"), "ReadScalar");
    }
    if (30_000..40_000).contains(&id) {
        return (indexed(30_000, "quotient_identity_eval"), "Intermediate");
    }
    if (40_000..41_000).contains(&id) {
        return (indexed(40_000, "pcs_q_com"), "Intermediate");
    }
    if (41_000..42_000).contains(&id) {
        return (indexed(41_000, "pcs_point_set"), "Intermediate");
    }
    if (60_000..61_000).contains(&id) {
        return (indexed(60_000, "selector_fold"), "Intermediate");
    }
    (format!("unknown[{id}]"), "Intermediate")
}

/// One {hex-key, id, kind, tag} record of the flat trace container.
fn trace_record(id: u64, tag: &str, kind: &str, data: &[u8]) -> Json {
    let mut map = Map::new();
    // 32-byte payloads are field elements; wider ones are the EIP-2537 padded
    // point slots (64 / 96 / 128 bytes) as the tracer serialised them.
    let key = if data.len() == 32 {
        "fe_be_hex"
    } else {
        "eip2537_hex"
    };
    map.insert(key.to_string(), json!(hex::encode(data)));
    map.insert("id".to_string(), json!(id));
    map.insert("kind".to_string(), json!(kind));
    map.insert("tag".to_string(), json!(tag));
    Json::Object(map)
}

/// The trace LOGs of the traced render, in emission order, as (id, payload).
fn traced_logs(logs: &[halo2_solidity_verifier::revm::primitives::Log]) -> Vec<(u64, Vec<u8>)> {
    let mut out = Vec::new();
    for log in logs {
        let data = log.data.data.as_ref();
        if data.is_empty() {
            continue;
        }
        let topics = log.data.topics();
        assert_eq!(topics.len(), 1, "trace log must have exactly one topic");
        let id =
            u64::from_be_bytes(topics[0].as_slice()[24..32].try_into().expect("topic is 32 bytes"));
        out.push((id, data.to_vec()));
    }
    out
}

/// solidity_trace.json: the LOG stream of the traced render as a flat
/// {kind, tag, id, *_hex} array.
fn solidity_trace_records(traced: &[(u64, Vec<u8>)]) -> Vec<Json> {
    traced
        .iter()
        .map(|(id, data)| {
            let (tag, kind) = yul_trace_name(*id);
            trace_record(*id, &tag, kind, data)
        })
        .collect()
}

/// verifier_trace.bin: MTR1 + u32 BE count, then one
/// "u32 BE name len | name | u32 BE data len | data" record per trace log, where
/// the name is "yul_trace.<tag>#<id>".
fn write_verifier_trace_bin(path: &Path, traced: &[(u64, Vec<u8>)]) {
    let mut out: Vec<u8> = Vec::new();
    out.extend_from_slice(b"MTR1");
    out.extend_from_slice(&(traced.len() as u32).to_be_bytes());
    for (id, data) in traced {
        let (tag, _) = yul_trace_name(*id);
        let name = format!("yul_trace.{tag}#{id}");
        out.extend_from_slice(&(name.len() as u32).to_be_bytes());
        out.extend_from_slice(name.as_bytes());
        out.extend_from_slice(&(data.len() as u32).to_be_bytes());
        out.extend_from_slice(data);
    }
    fs::write(path, out).expect("write verifier_trace.bin");
}

/// rust_trace.json: {"entries":[{"kind","data":{...}}]} from the live native
/// trace of the accepted run. proof_* names are indexed per name; challenges
/// carry "name" instead of "tag".
fn rust_trace_json(run: &Regenerated) -> Json {
    let mut entries = Vec::new();
    let vk_repr = <F as Hashable<Keccak256>>::to_input(&run.vk.vk().transcript_repr());
    let mut head = Map::new();
    head.insert("fe_be_hex".to_string(), json!(hex::encode(&vk_repr)));
    head.insert("tag".to_string(), json!("vk_repr"));
    entries.push(json!({"kind": "Intermediate", "data": Json::Object(head)}));

    let mut counters: BTreeMap<&str, usize> = BTreeMap::new();
    for event in &run.native_events {
        let is_challenge = (7..=16).contains(&event.id);
        let is_proof_read = event.name.starts_with("proof_");
        let kind = if is_challenge {
            "Challenge"
        } else if is_proof_read && event.data.len() == 128 {
            "ReadPoint"
        } else if is_proof_read {
            "ReadScalar"
        } else {
            "Intermediate"
        };
        let tag = if is_proof_read {
            let n = counters.entry(event.name).or_insert(0);
            let tag = format!("{}[{}]", event.name, *n);
            *n += 1;
            tag
        } else {
            event.name.to_string()
        };
        let mut data = Map::new();
        match kind {
            "Challenge" => {
                data.insert("fe_be_hex".to_string(), json!(hex::encode(&event.data)));
                data.insert("name".to_string(), json!(tag));
            }
            "ReadPoint" => {
                data.insert("eip2537_hex".to_string(), json!(hex::encode(&event.data)));
                data.insert("tag".to_string(), json!(tag));
            }
            "ReadScalar" => {
                data.insert("fe_be_hex".to_string(), json!(hex::encode(&event.data)));
                data.insert("tag".to_string(), json!(tag));
            }
            _ => {
                data.insert("data_hex".to_string(), json!(hex::encode(&event.data)));
                data.insert("tag".to_string(), json!(tag));
            }
        }
        entries.push(json!({"kind": kind, "data": Json::Object(data)}));
    }
    json!({ "entries": entries })
}

/// instance.be: 32 bytes, big-endian canonical Fq - the transcript absorb form,
/// which is what the committed file holds (R-57: the committed file is genuinely
/// big-endian; the to_repr write in tests/poseidon_fixture.rs goes to a
/// *different* path and is the misnamed one - left alone here).
fn instance_be(instance: &F) -> Vec<u8> {
    <F as Hashable<Keccak256>>::to_input(instance)
}

fn committed_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures").join("poseidon")
}

fn out_dir() -> Option<PathBuf> {
    env::var(OUT_ENV).ok().map(PathBuf::from)
}

/// Print, per artefact, whether the regenerated bytes equal the committed ones.
///
/// A **report, never an assertion**: proof.bin and everything derived from it
/// (the three traces) legitimately move run to run under OsRng quotient-limb
/// blinding, while vk.bin and instance.be are deterministic. What this prints is
/// the finding formal/BASELINE.md records under "what the harness reproduces".
fn report_against_committed(dir: &Path, names: &[&str]) {
    eprintln!("[m0-regen] byte comparison against the committed fixture (report only):");
    for name in names {
        let (Ok(new), Ok(old)) = (
            fs::read(dir.join(name)),
            fs::read(committed_dir().join(name)),
        ) else {
            eprintln!("  {name:22} (nothing committed to compare against)");
            continue;
        };
        if new == old {
            eprintln!("  {name:22} BYTE-IDENTICAL ({} B)", new.len());
            continue;
        }
        let common = new.iter().zip(old.iter()).take_while(|(a, b)| a == b).count();
        eprintln!(
            "  {name:22} DIFFERS (regenerated {} B vs committed {} B; first {common} bytes agree)",
            new.len(),
            old.len()
        );
        if *name == "proof.bin" {
            eprintln!(
                "  {name:22}   expected: only the {PRE_BLINDING_PREFIX_BYTES}-byte pre-quotient \
                 prefix is repeatable; the tail is OsRng-blinded"
            );
        }
    }
}

/// Regenerate the six frozen poseidon artefacts into M0_OUT and prove they pass
/// the real verifiers. **Inert unless M0_OUT is set.**
///
/// The assertions are structural on purpose - see the module comment. Do not turn
/// them into a byte comparison against fixtures/poseidon/proof.bin; that test
/// would flake on every run.
#[test]
fn m0_regen_poseidon_fixtures() {
    let Some(dir) = out_dir() else {
        eprintln!(
            "skipping m0_regen_poseidon_fixtures: set {OUT_ENV}=<scratch dir> (and \
             {RUN_EVM_TESTS_ENV}=1) to re-emit the frozen poseidon fixture set"
        );
        return;
    };
    if !env_flag_enabled(RUN_EVM_TESTS_ENV) {
        eprintln!(
            "skipping m0_regen_poseidon_fixtures: {OUT_ENV} is set but {RUN_EVM_TESTS_ENV}=1 is \
             also required, because the acceptance legs deploy the generated verifier on revm"
        );
        return;
    }
    fs::create_dir_all(&dir).expect("create M0_OUT");
    assert!(
        pinned_solc_available(),
        "the pinned solc 0.8.30 must be available to regenerate the fixture \
         (proofs/solidity-verifier/.solc/solc; see scripts/install_pinned_solc.sh)"
    );

    let run = regenerate();
    let generator = SolidityGenerator::new(
        &run.srs,
        run.vk.vk(),
        GeneratorConfig::new(NUM_INSTANCES, NUM_COMMITTED_INSTANCES),
    );

    // Acceptance legs 1 and 2: the plain renders, both quotient lowerings.
    let (vm_gas, _) = verify_on_evm("Vm", &generator, &run, QuotientLowering::Vm, false);
    let (direct_gas, _) =
        verify_on_evm("Direct", &generator, &run, QuotientLowering::Direct, false);

    // Acceptance leg 3: the traced render, whose LOG stream is the fixture.
    let (_, logs) = verify_on_evm("traced Vm", &generator, &run, QuotientLowering::Vm, true);
    let traced = traced_logs(&logs);

    // ---- write the six artefacts ----------------------------------------
    fs::write(dir.join("proof.bin"), &run.proof).expect("write proof.bin");
    fs::write(dir.join("instance.be"), instance_be(&run.instance)).expect("write instance.be");
    fs::write(
        dir.join("vk.bin"),
        run.vk.vk().to_bytes(SerdeFormat::Processed),
    )
    .expect("write vk.bin");
    write_json(dir.join("rust_trace.json"), &rust_trace_json(&run));
    let records = solidity_trace_records(&traced);
    write_json(
        dir.join("solidity_trace.json"),
        &Json::Array(records.clone()),
    );
    write_verifier_trace_bin(&dir.join("verifier_trace.bin"), &traced);

    let traced_points = records.iter().filter(|e| e["kind"] == json!("ReadPoint")).count();
    let traced_scalars = records.iter().filter(|e| e["kind"] == json!("ReadScalar")).count();
    assert_eq!(
        traced_points, EXPECTED_POINT_READS,
        "the traced render must emit {EXPECTED_POINT_READS} proof-commitment records"
    );
    assert_eq!(
        traced_scalars, EXPECTED_SCALAR_READS,
        "the traced render must emit {EXPECTED_SCALAR_READS} proof-evaluation records"
    );

    eprintln!(
        "[m0-regen] profile: features evm,rust-verifier-trace (release), PoseidonExample k={K}, \
         witness seed {WITNESS_SEED}, prover rng {PROVER_RNG_SEED:#x}, SRS bls_filecoin_2p{K}, \
         pinned solc 0.8.30, revm Prague"
    );
    eprintln!(
        "[m0-regen] proof = {} B ({} point reads + {} scalar reads = {} transcript reads); \
         native ACCEPT; solidity Vm ACCEPT ({vm_gas} gas), Direct ACCEPT ({direct_gas} gas); \
         traced render = {} records; vk.bin = {} B; transcript_repr = {}",
        run.proof.len(),
        run.point_reads,
        run.scalar_reads,
        run.point_reads + run.scalar_reads,
        records.len(),
        fs::read(dir.join("vk.bin")).map(|b| b.len()).unwrap_or_default(),
        hex::encode(<F as Hashable<Keccak256>>::to_input(
            &run.vk.vk().transcript_repr()
        )),
    );
    eprintln!("[m0-regen] wrote 6 artefacts to {}", dir.display());
    report_against_committed(&dir, &FIXTURE_ARTEFACTS);
}

/// Replay a fixture directory's recorded bytes through the real verifier.
/// **Inert unless M0_REPLAY_DIR is set.** This is the leg that answers whether the
/// *committed* artefacts still pass, as opposed to a fresh run.
///
/// M0_EXPECT selects the expected verdict (ACCEPT, the default, or REJECT).
#[test]
fn m0_replay_directory() {
    let Some(dir) = env::var(REPLAY_DIR_ENV).ok().map(PathBuf::from) else {
        eprintln!(
            "skipping m0_replay_directory: set {REPLAY_DIR_ENV}=<fixture dir> to replay recorded \
             bytes through the real verifier"
        );
        return;
    };
    let expect = env::var(REPLAY_EXPECT_ENV).unwrap_or_else(|_| "ACCEPT".into());
    assert!(
        matches!(expect.as_str(), "ACCEPT" | "REJECT"),
        "{REPLAY_EXPECT_ENV} must be ACCEPT or REJECT, got {expect:?}"
    );

    let proof = fs::read(dir.join("proof.bin")).expect("M0_REPLAY_DIR/proof.bin");
    let instance_bytes = fs::read(dir.join("instance.be")).expect("M0_REPLAY_DIR/instance.be");
    assert_eq!(
        instance_bytes.len(),
        32,
        "{}: instance.be must be 32 bytes",
        dir.display()
    );
    // The committed convention is BIG-endian canonical Fq - the transcript absorb
    // form, and what R-57 verified by decoding. Decode BE first and do not fall
    // back silently: both byte orders of the committed file happen to be canonical
    // field elements, so an LE-first read decodes a *different* value and the
    // verifier then rejects a perfectly good proof with Error::Opening. The
    // ambiguity is reported, not hidden.
    let mut le = <F as PrimeField>::Repr::default();
    le.as_mut().copy_from_slice(&instance_bytes);
    let mut be = le;
    be.as_mut().reverse();
    let be_decoded = Option::<F>::from(F::from_repr(be));
    let le_decoded = Option::<F>::from(F::from_repr(le));
    let instance = be_decoded
        .or(le_decoded)
        .expect("instance.be must decode as a canonical Fq in some byte order");
    assert!(
        be_decoded.is_some(),
        "{}: instance.be is not a canonical Fq read big-endian, which is the recorded `instance.be` convention (R-57)",
        dir.display()
    );
    eprintln!(
        "[m0-replay] dir = {}; proof = {} bytes; instance.be decoded big-endian; the \
         little-endian reading also decodes to a different element: {}",
        dir.display(),
        proof.len(),
        le_decoded.is_some() && le_decoded != be_decoded
    );

    let srs_dir = env::var("SRS_DIR").unwrap_or_else(|_| {
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../zk_stdlib/examples/assets"
        )
        .to_string()
    });
    env::set_var("SRS_DIR", &srs_dir);
    let relation = PoseidonExample;
    let srs = srs_for_test(&relation, Some(K));
    let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);

    // Structural, not bytewise: the recorded proof must have the recorded shape.
    assert_eq!(
        proof.len(),
        EXPECTED_PROOF_LEN,
        "replay: the recorded proof must be {EXPECTED_PROOF_LEN} bytes (21 x 48 + 51 x 32); \
         anything else is a different feature profile, not a stale fixture"
    );

    let verdict = midnight_zk_stdlib::verify::<PoseidonExample, Keccak256>(
        &srs.verifier_params(),
        &vk,
        &instance,
        None,
        &proof,
    );
    let got = if verdict.is_ok() { "ACCEPT" } else { "REJECT" };
    if let Err(err) = &verdict {
        eprintln!("[m0-replay] native verifier = REJECT ({err:?})");
    }
    // Report, do not assume, whether the recorded VK container is the one this
    // tree writes.
    let recorded_vk = fs::read(dir.join("vk.bin")).unwrap_or_default();
    let current_vk = vk.vk().to_bytes(SerdeFormat::Processed);
    eprintln!(
        "[m0-replay] vk.bin equals the current VK in SerdeFormat::Processed: {} \
         (recorded {} B, current {} B)",
        recorded_vk == current_vk,
        recorded_vk.len(),
        current_vk.len()
    );
    eprintln!("[m0-replay] native verifier verdict = {got}");
    assert_eq!(
        got, expect,
        "the fixture under {REPLAY_DIR_ENV} must be {expect}ed by the real verifier"
    );
}

fn write_json(path: PathBuf, value: &Json) {
    let file = File::create(&path).unwrap_or_else(|e| panic!("create {}: {e}", path.display()));
    let mut w = BufWriter::new(file);
    serde_json::to_writer_pretty(&mut w, value).expect("serialize json");
    w.flush().expect("flush json");
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
