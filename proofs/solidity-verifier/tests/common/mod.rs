//! In-process EVM harness that compiles + executes the poseidon Solidity
//! verifier through `revm` so property tests can invoke `verify()` without
//! paying the ~20s cost of spawning `forge test` per iteration.
//!
//! The harness assumes `forge build` has already produced fresh artifacts
//! under `out/` (or lazily calls it on first use via [`ensure_build`]); it
//! then:
//!
//!   1. Loads creation bytecode for `PoseidonVerifyingKey` and
//!      `PoseidonVerifier` from the Foundry JSON artifacts.
//!   2. Deploys the VK contract (constructor-less, returns a blob via
//!      `RETURN`, which becomes the account's runtime bytecode).
//!   3. Deploys the verifier with the VK address as constructor arg.
//!   4. Exposes `verify(instance, proof) -> bool` and
//!      `verify_raw(calldata) -> (success, output)` for malformed-input
//!      tests.
//!
//! Chain spec: the default `Context::mainnet()` uses the latest hard-fork,
//! which includes the EIP-2537 BLS12-381 precompiles. The `blst` feature
//! of `revm` is enabled so those precompiles use the fast blst backend.

use std::{fs, path::PathBuf, process::Command};

use revm::{
    context::{BlockEnv, CfgEnv, Context, TxEnv},
    context_interface::result::{ExecutionResult, Output},
    database::CacheDB,
    database_interface::EmptyDB,
    primitives::{Address, Bytes, TxKind, U256},
    state::Bytecode,
    ExecuteCommitEvm, MainBuilder, MainContext, MainnetEvm,
};

type Db = CacheDB<EmptyDB>;
type EvmCtx = Context<BlockEnv, TxEnv, CfgEnv, Db>;
type Evm = MainnetEvm<EvmCtx>;

fn artifact_path(root: &PathBuf, file: &str, contract: &str) -> PathBuf {
    root.join("out").join(file).join(format!("{contract}.json"))
}

fn load_creation_bytecode(path: &PathBuf) -> Vec<u8> {
    let j: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path:?}: {e}")),
    )
    .unwrap_or_else(|e| panic!("parse {path:?}: {e}"));
    let s = j["bytecode"]["object"]
        .as_str()
        .unwrap_or_else(|| panic!("missing bytecode.object in {path:?}"));
    let s = s.strip_prefix("0x").unwrap_or(s);
    hex::decode(s).unwrap_or_else(|e| panic!("hex decode {path:?}: {e}"))
}

pub fn root_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Per-circuit artifact layout — picked up by [`Harness::fresh_with`]
/// so the same revm-driven harness can mount either the poseidon VK
/// or the RSA-signature VK behind the generic `PlonkVerifier`.
#[derive(Clone, Copy)]
pub struct Circuit {
    /// `.sol` filename passed to `forge build`, relative to
    /// `contracts/` (so forge's `out/<file>/<contract>.json` path
    /// is built from this).
    pub vk_sol: &'static str,
    pub vk_contract: &'static str,
    /// Fixture directory name under `fixtures/`.
    pub fixtures_subdir: &'static str,
}

pub const POSEIDON: Circuit = Circuit {
    vk_sol: "PoseidonVerifyingKey.sol",
    vk_contract: "PoseidonVerifyingKey",
    fixtures_subdir: "poseidon",
};

pub const RSA_SIGNATURE: Circuit = Circuit {
    vk_sol: "RsaSignatureVerifyingKey.sol",
    vk_contract: "RsaSignatureVerifyingKey",
    fixtures_subdir: "rsa_signature",
};

pub const IVC: Circuit = Circuit {
    vk_sol: "IvcVerifyingKey.sol",
    vk_contract: "IvcVerifyingKey",
    fixtures_subdir: "ivc",
};

/// Run `forge build` if Foundry artifacts are missing.
pub fn ensure_build(force: bool) {
    let verifier_art = artifact_path(&root_dir(), "PlonkVerifier.sol", "PlonkVerifier");
    let vk_art = artifact_path(
        &root_dir(),
        POSEIDON.vk_sol,
        POSEIDON.vk_contract,
    );
    if !force && verifier_art.exists() && vk_art.exists() {
        return;
    }
    let status = Command::new("forge")
        .args(["build"])
        .current_dir(root_dir())
        .status()
        .expect("spawn forge build");
    assert!(status.success(), "forge build failed");
}

pub fn selector(sig: &str) -> [u8; 4] {
    use sha3::{Digest, Keccak256};
    let h = Keccak256::digest(sig.as_bytes());
    let mut out = [0u8; 4];
    out.copy_from_slice(&h[..4]);
    out
}

/// ABI calldata for `verify(bytes32[] publicInputs, bytes proof)`.
///
/// Layout (head + tail regions are separated by the `// ---` comment):
/// ```
/// [0..4]    selector("verify(bytes32[],bytes)")
/// [4..36]   offset of publicInputs head word (0x40)
/// [36..68]  offset of proof head word (0x60 + 32 * publicInputs.len())
/// // ---
/// [head[pi]] publicInputs.len() as u256 (big-endian)
/// [head[pi] + 32 * i] publicInputs[i]
/// [head[proof]]       proof.len() as u256 (big-endian)
/// [head[proof] + 32] proof bytes, zero-padded to a multiple of 32
/// ```
pub fn encode_verify_calldata(public_inputs: &[[u8; 32]], proof: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(
        4 + 32 + 32 + 32 + 32 * public_inputs.len() + 32 + proof.len() + 31,
    );
    out.extend_from_slice(&selector("verify(bytes32[],bytes)"));

    // Head: two offsets (always 32 bytes apart at the start of calldata).
    let pi_head_off: u64 = 0x40;
    let proof_head_off: u64 = pi_head_off + 32 + 32 * public_inputs.len() as u64;
    let mut buf = [0u8; 32];
    buf[24..32].copy_from_slice(&pi_head_off.to_be_bytes());
    out.extend_from_slice(&buf);
    buf = [0u8; 32];
    buf[24..32].copy_from_slice(&proof_head_off.to_be_bytes());
    out.extend_from_slice(&buf);

    // Tail 1: publicInputs.len() then each element.
    let mut plen = [0u8; 32];
    plen[24..32].copy_from_slice(&(public_inputs.len() as u64).to_be_bytes());
    out.extend_from_slice(&plen);
    for pi in public_inputs {
        out.extend_from_slice(pi);
    }

    // Tail 2: proof.len() then zero-padded proof bytes.
    let mut plen = [0u8; 32];
    let n = proof.len() as u64;
    plen[24..32].copy_from_slice(&n.to_be_bytes());
    out.extend_from_slice(&plen);
    out.extend_from_slice(proof);
    let rem = proof.len() % 32;
    if rem != 0 {
        out.extend(std::iter::repeat(0u8).take(32 - rem));
    }
    out
}

pub struct Deployed {
    pub vk_addr: Address,
    pub verifier_addr: Address,
    pub vk_runtime_code: Vec<u8>,
}

pub struct Harness {
    evm: Evm,
    caller: Address,
    nonce: u64,
}

impl Harness {
    pub fn fresh() -> (Self, Deployed) {
        Self::fresh_with(None, None)
    }

    /// Back-compat wrapper: deploys the poseidon VK against the
    /// generic `PlonkVerifier`.  RSA-targeted tests should call
    /// [`Harness::fresh_for`] directly.
    pub fn fresh_with(
        vk_runtime_override: Option<Vec<u8>>,
        verifier_creation_override: Option<Vec<u8>>,
    ) -> (Self, Deployed) {
        Self::fresh_for(POSEIDON, vk_runtime_override, verifier_creation_override)
    }

    /// Deploy the generic `PlonkVerifier` wired to whichever circuit's
    /// VK blob is requested.  `vk_runtime_override` allows the
    /// adversarial tests to replace the deployed VK bytes post-deploy
    /// (mutated-VK scenarios); `verifier_creation_override` likewise
    /// allows swapping the verifier creation bytecode.
    pub fn fresh_for(
        circuit: Circuit,
        vk_runtime_override: Option<Vec<u8>>,
        verifier_creation_override: Option<Vec<u8>>,
    ) -> (Self, Deployed) {
        ensure_build(false);

        let root = root_dir();
        let vk_creation = load_creation_bytecode(&artifact_path(
            &root,
            circuit.vk_sol,
            circuit.vk_contract,
        ));
        let verifier_creation = verifier_creation_override.unwrap_or_else(|| {
            load_creation_bytecode(&artifact_path(
                &root,
                "PlonkVerifier.sol",
                "PlonkVerifier",
            ))
        });

        let ctx = Context::mainnet().with_db(Db::default());
        let mut evm: Evm = ctx.build_mainnet();

        // Raise the EIP-7825 tx gas cap so the full verify() call fits
        // (the Solidity verifier needs ~13-15M gas; the default cap on
        // the latest hard-fork is 2^24 ≈ 16.7M).
        evm.ctx.cfg.tx_gas_limit_cap = Some(1 << 30);
        // The verifier's deployed bytecode is ~47 KB, which exceeds
        // EIP-170's 24 KB limit. Foundry raises this in test profiles;
        // mirror that here so `forge build` → revm deploy works.
        evm.ctx.cfg.limit_contract_code_size = Some(1 << 20);

        let caller = Address::from([0xa1; 20]);
        {
            use revm::state::AccountInfo;
            evm.ctx.journaled_state.database.insert_account_info(
                caller,
                AccountInfo {
                    balance: U256::from(10u128.pow(20)),
                    nonce: 0,
                    ..Default::default()
                },
            );
        }

        let mut nonce = 0u64;

        let vk_addr = deploy(&mut evm, caller, nonce, vk_creation.into());
        nonce += 1;

        let vk_runtime_code = if let Some(custom) = vk_runtime_override {
            set_account_code(&mut evm, vk_addr, &custom);
            custom
        } else {
            account_code(&evm, vk_addr)
        };

        let mut creation = verifier_creation;
        let mut ctor_arg = [0u8; 32];
        ctor_arg[12..32].copy_from_slice(vk_addr.as_slice());
        creation.extend_from_slice(&ctor_arg);
        let verifier_addr = deploy(&mut evm, caller, nonce, creation.into());
        nonce += 1;

        (
            Self { evm, caller, nonce },
            Deployed {
                vk_addr,
                verifier_addr,
                vk_runtime_code,
            },
        )
    }

    /// Low-level call. Returns `(success, output_bytes)`. Revert → `(false, revert_data)`.
    pub fn call_raw(&mut self, to: Address, data: Vec<u8>) -> (bool, Vec<u8>) {
        self.call_raw_with_gas(to, data, 30_000_000)
    }

    /// Like [`call_raw`] but with a caller-supplied gas budget. The IVC
    /// circuit produces a 110-element public-input vector and therefore
    /// pushes Lagrange-eval workloads beyond the 30 M default cap, so
    /// `tests/ivc.rs` opts into a 1 G budget.
    pub fn call_raw_with_gas(
        &mut self,
        to: Address,
        data: Vec<u8>,
        gas_limit: u64,
    ) -> (bool, Vec<u8>) {
        let tx = TxEnv::builder()
            .caller(self.caller)
            .kind(TxKind::Call(to))
            .data(Bytes::from(data))
            .nonce(self.nonce)
            .gas_limit(gas_limit)
            .build()
            .expect("build call tx");
        self.nonce += 1;
        let rx = self.evm.transact_commit(tx).expect("transact_commit");
        match rx {
            ExecutionResult::Success { output, .. } => {
                let bytes = match output {
                    Output::Call(b) => b.to_vec(),
                    Output::Create(b, _) => b.to_vec(),
                };
                (true, bytes)
            }
            ExecutionResult::Revert { output, .. } => (false, output.to_vec()),
            ExecutionResult::Halt { .. } => (false, Vec::new()),
        }
    }

    pub fn verify(&mut self, dep: &Deployed, instance: [u8; 32], proof: &[u8]) -> bool {
        let pis = [instance];
        self.verify_multi(dep, &pis, proof)
    }

    /// Phase-2 generic entry: for circuits whose single non-committed
    /// instance column holds more than one Fq value (e.g. RSA).
    pub fn verify_multi(
        &mut self,
        dep: &Deployed,
        public_inputs: &[[u8; 32]],
        proof: &[u8],
    ) -> bool {
        let cd = encode_verify_calldata(public_inputs, proof);
        let (ok, out) = self.call_raw(dep.verifier_addr, cd);
        Self::raw_is_accept(ok, &out)
    }

    pub fn verify_raw(
        &mut self,
        dep: &Deployed,
        calldata: Vec<u8>,
    ) -> (bool, Vec<u8>) {
        self.call_raw(dep.verifier_addr, calldata)
    }

    /// A raw verifier output counts as acceptance iff the call succeeded
    /// AND the first returned word is non-zero.
    pub fn raw_is_accept(ok: bool, out: &[u8]) -> bool {
        ok && out.len() >= 32 && out[..32].iter().any(|b| *b != 0)
    }
}

fn deploy(evm: &mut Evm, caller: Address, nonce: u64, data: Bytes) -> Address {
    let tx = TxEnv::builder()
        .caller(caller)
        .kind(TxKind::Create)
        .data(data)
        .nonce(nonce)
        .gas_limit(30_000_000)
        .build()
        .expect("build tx");
    let rx = evm.transact_commit(tx).expect("transact_commit");
    match rx {
        ExecutionResult::Success {
            output: Output::Create(_, Some(addr)),
            ..
        } => addr,
        other => panic!("deploy failed: {other:#?}"),
    }
}

fn account_code(evm: &Evm, addr: Address) -> Vec<u8> {
    let db = &evm.ctx.journaled_state.database;
    let acc = db.cache.accounts.get(&addr).expect("account missing");
    acc.info
        .code
        .as_ref()
        .map(|bc| bc.original_bytes().to_vec())
        .unwrap_or_default()
}

fn set_account_code(evm: &mut Evm, addr: Address, code: &[u8]) {
    use revm::primitives::keccak256;
    let db = &mut evm.ctx.journaled_state.database;
    let acc = db.cache.accounts.get_mut(&addr).expect("account missing");
    let bc = Bytecode::new_raw(Bytes::from(code.to_vec()));
    acc.info.code_hash = keccak256(code);
    acc.info.code = Some(bc);
}

/// Flip one nibble near the middle of the first `hex"..."` literal in the
/// given `.sol` source.
pub fn mutate_first_large_hex_literal(src: &str) -> String {
    let needle = "hex\"";
    let start = src.find(needle).expect("no hex literal in source");
    let body_start = start + needle.len();
    let body_end = src[body_start..]
        .find('"')
        .expect("unterminated hex literal");
    let abs_end = body_start + body_end;
    let body = &src[body_start..abs_end];
    assert!(
        body.len() >= 64,
        "hex literal too short to mutate ({} chars)",
        body.len()
    );
    let mid = body_start + (body.len() / 2);
    let ch = src.as_bytes()[mid] as char;
    let new_ch = match ch {
        '0'..='8' | 'a'..='e' => char::from_u32(ch as u32 + 1).unwrap(),
        _ => '0',
    };
    let mut out = String::with_capacity(src.len());
    out.push_str(&src[..mid]);
    out.push(new_ch);
    out.push_str(&src[mid + 1..]);
    out
}

/// Overwrite the 32-byte word at `offset` (relative to calldata start)
/// with the big-endian encoding of `value` (right-aligned).
pub fn overwrite_u256_word(calldata: &mut [u8], offset: usize, value: u64) {
    let mut w = [0u8; 32];
    w[24..32].copy_from_slice(&value.to_be_bytes());
    calldata[offset..offset + 32].copy_from_slice(&w);
}
