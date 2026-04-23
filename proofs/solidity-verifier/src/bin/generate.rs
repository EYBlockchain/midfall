//! Generate Solidity contracts + fixture files for the poseidon example.
//!
//! Running `cargo run --bin generate` will:
//!   1. Build the SRS, keygen VK/PK, and prove the poseidon circuit using
//!      the Keccak256 transcript.
//!   2. Dump the proof, instance, and execution trace to `fixtures/`.
//!   3. Render `contracts/PoseidonVerifyingKey.sol` with the runtime data.
//!
//! The verifier contract `contracts/PoseidonVerifier.sol` is *not*
//! regenerated — its logic is circuit-agnostic within the constraints baked
//! into the VK blob. Only the VK contract depends on the circuit.

use std::{fs, io::Write, path::PathBuf};

use midnight_curves::Fq;
use midnight_solidity_verifier::{
    codegen::{render_verifying_key, VkInfo},
    eip2537::fq_to_be,
    poseidon_fixture::PoseidonFixture,
};

fn main() {
    let here: PathBuf = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .expect("CARGO_MANIFEST_DIR");
    let fixtures = here.join("fixtures");
    let contracts = here.join("contracts");
    fs::create_dir_all(&fixtures).expect("mkdir fixtures");
    fs::create_dir_all(&contracts).expect("mkdir contracts");

    let k = std::env::var("POSEIDON_K").ok().and_then(|s| s.parse().ok()).unwrap_or(6u32);
    let seed: u64 = std::env::var("POSEIDON_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(1);

    eprintln!("[1/4] building poseidon proof (k={k}, seed={seed})");
    let fx = PoseidonFixture::build(k, seed);

    eprintln!("[2/4] extracting VK info");
    let vk_info = VkInfo::from_live(fx.vk.vk(), &fx.srs);

    eprintln!(
        "      k={} n={} cs_degree={} blinding={}\n      fixed_cols={} perm_cols={} advice_cols={} inst_cols={} challenges={} phases={} simple_sels={}\n      advice_q={} fixed_q={} inst_q={}\n      lookups={} trashcans={} perm_chunks={} quotient_limbs={}\n      proof_size={} bytes",
        vk_info.k, vk_info.n, vk_info.cs_degree, vk_info.blinding_factors,
        vk_info.num_fixed_columns,
        vk_info.num_permutation_columns,
        vk_info.num_advice_columns,
        vk_info.num_instance_columns,
        vk_info.num_challenges,
        vk_info.num_phases,
        vk_info.num_simple_selectors,
        vk_info.num_advice_queries,
        vk_info.num_fixed_queries,
        vk_info.num_instance_queries,
        vk_info.num_lookups,
        vk_info.num_trashcans,
        vk_info.num_permutation_chunks,
        vk_info.num_quotient_limbs,
        fx.proof.len(),
    );

    eprintln!("[3/4] writing Solidity VK contract");
    let sol = render_verifying_key(&vk_info);
    fs::write(contracts.join("PoseidonVerifyingKey.sol"), sol).expect("write sol");

    eprintln!("[4/4] dumping proof + instance");
    fs::write(fixtures.join("proof.bin"), &fx.proof).expect("write proof");
    fs::write(fixtures.join("instance.be"), fq_to_be(&fx.instance)).expect("write instance");

    // Also dump the VK blob separately so tests don't have to deploy the VK
    // contract when they just want to cross-check the byte layout.
    let mut blob = Vec::new();
    write_vk_blob(&vk_info, &mut blob);
    fs::write(fixtures.join("vk.bin"), blob).expect("write vk blob");

    // Also dump compressed bytes of the G1 identity for the Solidity side
    // to consume (instead of hard-coding 0xc0 || zeros and hoping the
    // BLS encoding matches).
    {
        use group::{Group, GroupEncoding};
        let id: midnight_curves::G1Projective =
            <midnight_curves::G1Projective as Group>::identity();
        let b = <midnight_curves::G1Projective as GroupEncoding>::to_bytes(&id);
        fs::write(fixtures.join("identity_g1_compressed.bin"), b.as_ref()).unwrap();
        eprintln!(
            "      G1 identity compressed = 0x{}",
            hex::encode(b.as_ref())
        );
    }

    // Emit algebra-primitive fixtures so the forge test can unit-test the
    // Solidity Fr/Lagrange/interpolation helpers against blst/midnight-
    // proofs before relying on them from the full verifier.
    //
    // File layout (big-endian, all scalars 32 bytes):
    //   fixtures/algebra_fixtures.bin:
    //       [0  .. 32)   omega
    //       [32 .. 64)   n (as an Fr element)
    //       [64 .. 96)   x  (random challenge)
    //       [96 ..128)   xn = x^n
    //       [128..160)   a  (random Fr)
    //       [160..192)   a_inv
    //       [192..224)   nb_lagrange_evals N (uint256 BE)
    //       [224.. ... ) L_0(x), L_1(x), ..., L_{N-1}(x)  (32 bytes each)
    {
        use ff::{Field, PrimeField};
        let domain = fx.vk.vk().get_domain();
        let omega = domain.get_omega();
        let n: u64 = vk_info.n;
        let n_fq = Fq::from(n);
        // Use a deterministic "random" x challenge independent of the proof
        // (constants chosen to match a future forge test fixture).
        let x_bytes: [u8; 32] = [
            0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,
            0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff,0x01,
            0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,
            0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,
        ];
        let x = {
            let mut le = x_bytes;
            le.reverse();
            Fq::from_repr(le).unwrap()
        };
        let xn = x.pow_vartime([n]);

        let a = Fq::from(0x1234_5678_9abc_defu64);
        let a_inv = a.invert().unwrap();

        // L_i(x) for i in 0..n (full domain).
        let lagrange_evals: Vec<Fq> =
            domain.l_i_range(x, xn, 0..(n as i32)).iter().copied().collect();

        let mut blob = Vec::new();
        blob.extend_from_slice(&fq_to_be(&omega));
        blob.extend_from_slice(&fq_to_be(&n_fq));
        blob.extend_from_slice(&fq_to_be(&x));
        blob.extend_from_slice(&fq_to_be(&xn));
        blob.extend_from_slice(&fq_to_be(&a));
        blob.extend_from_slice(&fq_to_be(&a_inv));
        // Pad u64 big-endian length to a full 32-byte word MSB-first so that
        // Solidity's `mload` (big-endian uint256) sees the length directly.
        blob.extend_from_slice(&[0u8; 24]);
        blob.extend_from_slice(&(lagrange_evals.len() as u64).to_be_bytes());
        for e in &lagrange_evals { blob.extend_from_slice(&fq_to_be(e)); }
        fs::write(fixtures.join("algebra_fixtures.bin"), &blob).unwrap();
        eprintln!(
            "      algebra fixtures written ({} bytes, {} Lagrange evals)",
            blob.len(),
            lagrange_evals.len(),
        );
    }

    // Emit a (compressed, EIP-2537 uncompressed) fixture pair for each of
    // the proof's G1 points. The forge test uses these to unit-test the
    // Solidity decompression function before attempting the full pairing.
    {
        use group::{Group, GroupEncoding};
        let mut pairs: Vec<u8> = Vec::new();
        let mut write_pair = |p: &midnight_curves::G1Projective| {
            let c: <midnight_curves::G1Projective as GroupEncoding>::Repr =
                <midnight_curves::G1Projective as GroupEncoding>::to_bytes(p);
            let u = midnight_solidity_verifier::eip2537::g1_projective_to_eip2537(p);
            pairs.extend_from_slice(c.as_ref()); // 48 bytes
            pairs.extend_from_slice(&u);         // 128 bytes
        };

        // Use the SRS generator and two random-ish points from the fixed
        // commitments as test vectors.
        write_pair(&<midnight_curves::G1Projective as Group>::generator());
        for c in fx.vk.vk().fixed_commitments().iter().take(3) {
            write_pair(c);
        }
        fs::write(fixtures.join("decomp_pairs.bin"), &pairs).unwrap();
        eprintln!(
            "      decomp fixture pairs written ({} bytes = {} x (48+128))",
            pairs.len(),
            pairs.len() / 176,
        );
    }

    eprintln!("OK — see {}/ for generated files", contracts.display());
    eprintln!("         {}/ for fixtures", fixtures.display());
}

fn write_vk_blob(vk: &VkInfo, out: &mut impl Write) {
    out.write_all(&vk.transcript_repr_be).unwrap();
    out.write_all(&vk.omega_be).unwrap();

    let mut c1 = [0u8; 32];
    c1[0..8].copy_from_slice(&vk.n.to_be_bytes());
    c1[8..12].copy_from_slice(&vk.k.to_be_bytes());
    c1[12..16].copy_from_slice(&(vk.num_advice_columns as u32).to_be_bytes());
    c1[16..20].copy_from_slice(&(vk.num_fixed_columns as u32).to_be_bytes());
    c1[20..24].copy_from_slice(&(vk.num_instance_columns as u32).to_be_bytes());
    c1[24..28].copy_from_slice(&(vk.num_challenges as u32).to_be_bytes());
    c1[28..32].copy_from_slice(&(vk.num_phases as u32).to_be_bytes());
    out.write_all(&c1).unwrap();

    let mut c2 = [0u8; 32];
    c2[0..4].copy_from_slice(&(vk.cs_degree as u32).to_be_bytes());
    c2[4..8].copy_from_slice(&(vk.num_simple_selectors as u32).to_be_bytes());
    c2[8..12].copy_from_slice(&(vk.blinding_factors as u32).to_be_bytes());
    c2[12..16].copy_from_slice(&(vk.num_advice_queries as u32).to_be_bytes());
    c2[16..20].copy_from_slice(&(vk.num_fixed_queries as u32).to_be_bytes());
    c2[20..24].copy_from_slice(&(vk.num_instance_queries as u32).to_be_bytes());
    c2[24..28].copy_from_slice(&(vk.num_lookups as u32).to_be_bytes());
    c2[28..32].copy_from_slice(&(vk.num_trashcans as u32).to_be_bytes());
    out.write_all(&c2).unwrap();

    let total_lookup_helpers: u32 = vk.lookup_num_chunks.iter().map(|&c| c as u32).sum();
    let mut c3 = [0u8; 32];
    c3[0..4].copy_from_slice(&(vk.num_permutation_columns as u32).to_be_bytes());
    c3[4..8].copy_from_slice(&(vk.num_permutation_chunks as u32).to_be_bytes());
    c3[8..12].copy_from_slice(&(vk.num_quotient_limbs as u32).to_be_bytes());
    c3[12..16].copy_from_slice(&total_lookup_helpers.to_be_bytes());
    c3[16..20].copy_from_slice(&(vk.num_committed_instance_evals as u32).to_be_bytes());
    out.write_all(&c3).unwrap();

    for c in &vk.fixed_comms_eip2537 { out.write_all(c).unwrap(); }
    for c in &vk.perm_comms_eip2537  { out.write_all(c).unwrap(); }
    out.write_all(&vk.s_g2_eip2537).unwrap();
    out.write_all(&vk.neg_g2_eip2537).unwrap();
}
