// SPDX-License-Identifier: CC0-1.0

// Pinned to match the verifier, so both halves of a deployment are provably
// built by one toolchain. (This contract's runtime is pure returned data, so
// its codehash is compiler-independent -- the pin is for the pair, not for it.)
pragma solidity 0.8.30;

/// @title Halo2 BLS12-381 verifying-key payload.
/// @notice Contract whose deployed runtime is `INVALID || generated verifier-key payload`.
/// @dev Byte 0 is an unconditional INVALID opcode so direct calls cannot execute payload bytes as code. The linked verifier pins the full runtime by length/codehash and copies the payload starting at byte 1.
/// @dev The layout follows the verifier inputs derived from
/// `midfall/proofs/src/plonk/mod.rs::VerifyingKey` and the transcript
/// `vk.hash_into` behavior used by `midfall/proofs/src/plonk/verifier.rs`.
///
/// Layout (in 32-byte words, big-endian). The header slots are generated from
/// Rust's `VkHeaderLayout`; the byte offsets are absolute from the start of the
/// VK payload, not from byte 0 of the runtime. Runtime byte 0 is the INVALID
/// prefix; the verifier loads the payload via
/// `extcodecopy(vk, VK_MPTR, 0x01, vk_payload_len)` and then references each
/// slot by `VK_MPTR + i`.
///
///   word  0  : vk_digest                    (Fq, transcript_repr of the CS)
///   word  1  : num_instances
///   word  2  : k                            (log2 of the domain size)
///   word  3  : n_inv                        (1/n in Fr)
///   word  4  : omega                        (n-th primitive root of unity)
///   word  5  : omega_inv
///   word  6  : omega_inv_to_l               (omega_inv ^ |rotation_last|)
///   word  7  : has_accumulator              (0 or 1)
///   word  8  : acc_offset                   (instance index of the accumulator)
///   word  9  : num_acc_limbs
///   word 10  : num_acc_limb_bits
///   word 11..14 : G1_BASE                   (4 words, EIP-2537 padded)
///   word 15..22 : G2_BASE                   (8 words, EIP-2537 padded)
///   word 23..30 : NEG_S_G2_BASE             (8 words, EIP-2537 padded)
///   word 31..30 + Q_PAYLOAD      : quotient VM constants + packed bytecode
///   word 31 + Q_PAYLOAD ..       : fixed_comms (4 words each)
///   word 31 + Q_PAYLOAD + 4*N_FIXED ..
///                                : permutation_comms (4 words each)
///
/// Notes:
/// - `extcodehash` of this contract is pinned by the linked verifier via
///   `EXPECTED_VK_CODEHASH`, so any byte tweak is detected at deploy time.
/// - The quotient identity interpreter's static program is stored in this
///   pinned VK runtime. The verifier reads it from memory after `extcodecopy`,
///   avoiding verifier-side PUSH32/mstore immediates while keeping the program
///   covered by `EXPECTED_VK_CODEHASH`.
/// - The midnight-proofs migration bakes the per-lookup chunk counts, trashcan
///   structure, and `num_simple_selectors` into the generated verifier code.
contract Halo2VerifyingKey {
    /// @notice Deploy the verifying-key payload as this contract's runtime bytecode.
    /// @dev The constructor writes an INVALID byte followed by generated words into memory and returns that prefixed runtime.
    /// @dev The transient construction buffer starts at `0x80`, preserving Solidity's reserved memory words.
    constructor() {
        assembly {
            // Runtime layout:
            //   byte 0      : INVALID, so the payload cannot be executed
            //   byte 1..end : generated VK payload copied by Halo2Verifier
            //
            // `runtime` includes the INVALID prefix; `payload` points to word
            // zero of the verifier-key data described in the contract NatSpec.
            let runtime := 0x80
            let payload := add(runtime, 0x01)
            mstore8(runtime, 0xfe)
            // Header, base-point, and quotient-program words generated from
            // VkPayloadLayout. The inline names on each mstore identify the
            // exact slot in the rendered source.
            mstore(add(payload, 0x0000), 0x5af31a14a32bd837cadc29fff8322c5f0633397b599cede9a0925b9f511186a4) // vk_digest
            mstore(add(payload, 0x0020), 0x0000000000000000000000000000000000000000000000000000000000000016) // num_instances
            mstore(add(payload, 0x0040), 0x000000000000000000000000000000000000000000000000000000000000000c) // k
            mstore(add(payload, 0x0060), 0x73e66878b46ae3705eb6a46a89213de7d3686828bfce5c19400fffff00100001) // n_inv
            mstore(add(payload, 0x0080), 0x564c0a11a0f704f4fc3e8acfe0f8245f0ad1347b378fbf96e206da11a5d36306) // omega
            mstore(add(payload, 0x00a0), 0x391b2856c609b4784ae25ffab9dc59865046d17864183203961a252dd8543362) // omega_inv
            mstore(add(payload, 0x00c0), 0x6a61dbd781fc6d1c881dab49e15d37277dd34dc48b542a7916654b4e3193f385) // omega_inv_to_l
            mstore(add(payload, 0x00e0), 0x0000000000000000000000000000000000000000000000000000000000000000) // has_accumulator
            mstore(add(payload, 0x0100), 0x0000000000000000000000000000000000000000000000000000000000000000) // acc_offset
            mstore(add(payload, 0x0120), 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limbs
            mstore(add(payload, 0x0140), 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limb_bits
            mstore(add(payload, 0x0160), 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f) // g1_x_hi
            mstore(add(payload, 0x0180), 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb) // g1_x_lo
            mstore(add(payload, 0x01a0), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4) // g1_y_hi
            mstore(add(payload, 0x01c0), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1) // g1_y_lo
            mstore(add(payload, 0x01e0), 0x00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051) // g2_x_c0_hi
            mstore(add(payload, 0x0200), 0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8) // g2_x_c0_lo
            mstore(add(payload, 0x0220), 0x0000000000000000000000000000000013e02b6052719f607dacd3a088274f65) // g2_x_c1_hi
            mstore(add(payload, 0x0240), 0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e) // g2_x_c1_lo
            mstore(add(payload, 0x0260), 0x000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351a) // g2_y_c0_hi
            mstore(add(payload, 0x0280), 0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801) // g2_y_c0_lo
            mstore(add(payload, 0x02a0), 0x000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99) // g2_y_c1_hi
            mstore(add(payload, 0x02c0), 0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be) // g2_y_c1_lo
            mstore(add(payload, 0x02e0), 0x00000000000000000000000000000000050ac27c3527072b81af0fa9a683e226) // neg_s_g2_x_c0_hi
            mstore(add(payload, 0x0300), 0xda79275f2985c9e89a0db969b76e0b6be94fee874c48586737ad5588cf1e1041) // neg_s_g2_x_c0_lo
            mstore(add(payload, 0x0320), 0x00000000000000000000000000000000116010f1b3d33aa5f3f608c385400979) // neg_s_g2_x_c1_hi
            mstore(add(payload, 0x0340), 0xed36dc3fab53d3626f519c74d7e1ebef62c9ad35796404ce2fc3ebb42167b5a1) // neg_s_g2_x_c1_lo
            mstore(add(payload, 0x0360), 0x0000000000000000000000000000000015b237e8c830b11d92578cb44ab0a93f) // neg_s_g2_y_c0_hi
            mstore(add(payload, 0x0380), 0x5176b4898e3a759bb6fba9e6c9375340a8a87557a3943686097db68d914e268e) // neg_s_g2_y_c0_lo
            mstore(add(payload, 0x03a0), 0x00000000000000000000000000000000006d57f79a18220d1e5ef04bd519e995) // neg_s_g2_y_c1_hi
            mstore(add(payload, 0x03c0), 0x9a9cc71553bb761b5422a6b6971b75c8d3695bfa07b861c4b1c958da426efc45) // neg_s_g2_y_c1_lo
            mstore(add(payload, 0x03e0), 0x1b0000191f000000000000000000000000000000000000000000000000000000) // quotient_program
            // Fixed-column commitment 0, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0400), 0x0000000000000000000000000000000015b3047638c1642a745e94d5f96a15ff) // fixed_comms[0].x_hi
            mstore(add(payload, 0x0420), 0xc0a49749f239ae6e482650af6c0a990b3d498c5142f7016ca4b9d3ce311a236b) // fixed_comms[0].x_lo
            mstore(add(payload, 0x0440), 0x0000000000000000000000000000000002fda5ca2d8eb50527cc98cc3e0e1f48) // fixed_comms[0].y_hi
            mstore(add(payload, 0x0460), 0xfea046001bf93de2ca832b09380edd8cda5a3ca7bcaab25e8217d164d3f31c46) // fixed_comms[0].y_lo
            // Fixed-column commitment 1, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0480), 0x000000000000000000000000000000000bfb65d12c8a5bcb6bee9f3862f1f9e5) // fixed_comms[1].x_hi
            mstore(add(payload, 0x04a0), 0xd873f3501304bedd6b5d28c0910b20cfd324ce32b378431974a9c3a6e9249c16) // fixed_comms[1].x_lo
            mstore(add(payload, 0x04c0), 0x00000000000000000000000000000000062d0e446164057f2ea372b2e4c4c934) // fixed_comms[1].y_hi
            mstore(add(payload, 0x04e0), 0x4b6a76e1a3571af219754242550cbcb85a559be283008ee32cb81d2d8a4da505) // fixed_comms[1].y_lo
            // Fixed-column commitment 2, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0500), 0x000000000000000000000000000000000350527faa0cec55462c301e1a1def8f) // fixed_comms[2].x_hi
            mstore(add(payload, 0x0520), 0xcea628cd1be49e70e35486aa5b5cea33a5d7db3e1fec1abc5d935e7ef35aec0d) // fixed_comms[2].x_lo
            mstore(add(payload, 0x0540), 0x0000000000000000000000000000000012f90def544e9214e22a45496e7c1037) // fixed_comms[2].y_hi
            mstore(add(payload, 0x0560), 0x154a6650167171244846c06b6cc82524a0aca6ee0c974e628d5981d87e375e2f) // fixed_comms[2].y_lo
            // Fixed-column commitment 3, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0580), 0x00000000000000000000000000000000111a09527e15ba2c44ca09a9db999ad7) // fixed_comms[3].x_hi
            mstore(add(payload, 0x05a0), 0x023829865c06973fe13209f32b12d0d6d4f2dd7dd79ceff0aa69c42ba87321c2) // fixed_comms[3].x_lo
            mstore(add(payload, 0x05c0), 0x00000000000000000000000000000000076a23e30d17266269fe3710b7c8f309) // fixed_comms[3].y_hi
            mstore(add(payload, 0x05e0), 0xdfe8d47cf975767422d90d4e02d62a9350c3ac40d10ea9714c17651196dd45eb) // fixed_comms[3].y_lo
            // Fixed-column commitment 4, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0600), 0x00000000000000000000000000000000002a33e626b69f15f79d8b65da885ff5) // fixed_comms[4].x_hi
            mstore(add(payload, 0x0620), 0x19294fba5e0843f7d082172e74a25010b359e1ff3515bc38f25532d490a27529) // fixed_comms[4].x_lo
            mstore(add(payload, 0x0640), 0x0000000000000000000000000000000009da3780ffa60b6c6c4fd510084adfc9) // fixed_comms[4].y_hi
            mstore(add(payload, 0x0660), 0xbd68273d86aaf54742724b0d0de60b1d05bd49cd7fc9e4be17b83f39ca822bb3) // fixed_comms[4].y_lo
            // Fixed-column commitment 5, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0680), 0x0000000000000000000000000000000000059bc2f3263e4821d710b717a3e0b2) // fixed_comms[5].x_hi
            mstore(add(payload, 0x06a0), 0xe9631c2232a30b977095264a69c8b27b78fc7d98193140f4821d149c29a4014f) // fixed_comms[5].x_lo
            mstore(add(payload, 0x06c0), 0x0000000000000000000000000000000001f6bcc5e10a398b7599657aac7c256f) // fixed_comms[5].y_hi
            mstore(add(payload, 0x06e0), 0xfb38cb0e65cd39330467e3eb5df26fa95adaa273a4e5167e14e48d06f6e199c9) // fixed_comms[5].y_lo
            // Fixed-column commitment 6, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0700), 0x000000000000000000000000000000000155f5088a284e988dc3c8f486fdd0e7) // fixed_comms[6].x_hi
            mstore(add(payload, 0x0720), 0xe518cbc6e9fccd8d09525cd59c16e2aff7c31d0eb4013b78a2859cdb0261a206) // fixed_comms[6].x_lo
            mstore(add(payload, 0x0740), 0x0000000000000000000000000000000016a26561166cabf5c2e834311b24781b) // fixed_comms[6].y_hi
            mstore(add(payload, 0x0760), 0x5a67e3443fcb9243062cf6987280319624644c4b7ceb1ec22324a574f8d7752e) // fixed_comms[6].y_lo
            // Fixed-column commitment 7, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0780), 0x0000000000000000000000000000000011ef5d7e41f054cb14ee4af99dc4dd51) // fixed_comms[7].x_hi
            mstore(add(payload, 0x07a0), 0x255304854288f70844bbdbb0ef601e6d1868c989e8746ee43d32ed4d7a98162c) // fixed_comms[7].x_lo
            mstore(add(payload, 0x07c0), 0x00000000000000000000000000000000050831e057ea76f7532384c26f4310b0) // fixed_comms[7].y_hi
            mstore(add(payload, 0x07e0), 0x7cee03cd7941faba220760d096320172eae3f1407139ad151a8cff120927ac30) // fixed_comms[7].y_lo
            // Fixed-column commitment 8, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0800), 0x00000000000000000000000000000000148512eeb2d5f37e9d4951152c1378b6) // fixed_comms[8].x_hi
            mstore(add(payload, 0x0820), 0x5734169456e0637e7321fbaf9dfdfd27c178b049a206b4dceb905afde6dc4394) // fixed_comms[8].x_lo
            mstore(add(payload, 0x0840), 0x0000000000000000000000000000000012d03749db1c1723cefc297f64c7b453) // fixed_comms[8].y_hi
            mstore(add(payload, 0x0860), 0x1a43c911fd1880e6a09a8b9c77c0cd13aa44161405cc668607058abec96693db) // fixed_comms[8].y_lo
            // Fixed-column commitment 9, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0880), 0x0000000000000000000000000000000016512f02244b462b769f3e7d1ab8a510) // fixed_comms[9].x_hi
            mstore(add(payload, 0x08a0), 0xd96a268575d865b0905436762c06b19ab16533cd8d98be49b787f5cdb23bffd9) // fixed_comms[9].x_lo
            mstore(add(payload, 0x08c0), 0x00000000000000000000000000000000154589ae7e2b7b005d279466533def35) // fixed_comms[9].y_hi
            mstore(add(payload, 0x08e0), 0x886b727a271c949eef557f04cd0ee7f6df14af8a2e3ddfd04801c00e72c9084a) // fixed_comms[9].y_lo
            // Fixed-column commitment 10, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0900), 0x000000000000000000000000000000000f3f75726975c682d4c2b4d57a77408a) // fixed_comms[10].x_hi
            mstore(add(payload, 0x0920), 0x4d1d668f6817f5806b4c9e6bafb2c18a929369c7a58601fd3b3932cfe21e02e7) // fixed_comms[10].x_lo
            mstore(add(payload, 0x0940), 0x0000000000000000000000000000000000b330cc2bfea16d7e926b6fc3da608a) // fixed_comms[10].y_hi
            mstore(add(payload, 0x0960), 0xfcc3539d203c0e4b62741ac4291fd9b926f1dc9978983692dc153c13a8f5db9c) // fixed_comms[10].y_lo
            // Fixed-column commitment 11, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0980), 0x000000000000000000000000000000000aced0959f8e6e9279f0c4117c50e6a5) // fixed_comms[11].x_hi
            mstore(add(payload, 0x09a0), 0x348095c060fe5dabec28c13e63cdb793a1db2ab3b2d84e02cd7c9b20a56b39f1) // fixed_comms[11].x_lo
            mstore(add(payload, 0x09c0), 0x0000000000000000000000000000000010e36e9b5bbafe4bc024b6a9dfff104e) // fixed_comms[11].y_hi
            mstore(add(payload, 0x09e0), 0xc3b37a60633cc8c6e6311da6aa59a6687156b2d16c35e4450e6c3fe08a74d0b2) // fixed_comms[11].y_lo
            // Fixed-column commitment 12, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0a00), 0x0000000000000000000000000000000016492390fa83afbdd8e88d1e2c57757f) // fixed_comms[12].x_hi
            mstore(add(payload, 0x0a20), 0xe6cf389fad579030902fbad9432b52319e7f7d90433b419092e5717390a09a02) // fixed_comms[12].x_lo
            mstore(add(payload, 0x0a40), 0x000000000000000000000000000000000b58474f3da048fdca4e26fe589ae615) // fixed_comms[12].y_hi
            mstore(add(payload, 0x0a60), 0x6840b799fb1ef1e35b32079b4c3e55c660f144eba8f002bd952e6d469cf91162) // fixed_comms[12].y_lo
            // Fixed-column commitment 13, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0a80), 0x0000000000000000000000000000000009669429b4d2cb6443693062b8a9ec2f) // fixed_comms[13].x_hi
            mstore(add(payload, 0x0aa0), 0x177fc226eb4152e8b55d34fe476b489fa07859eff65f5d99c4e9a822b7ae44ae) // fixed_comms[13].x_lo
            mstore(add(payload, 0x0ac0), 0x0000000000000000000000000000000013d3969d418f9e3b87d6a9da2f5f875c) // fixed_comms[13].y_hi
            mstore(add(payload, 0x0ae0), 0xfab8d37ad53ba0cc58cda438317d263befd2163ada0ba6ea6e4d74464432f9d1) // fixed_comms[13].y_lo
            // Fixed-column commitment 14, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0b00), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[14].x_hi
            mstore(add(payload, 0x0b20), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[14].x_lo
            mstore(add(payload, 0x0b40), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[14].y_hi
            mstore(add(payload, 0x0b60), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[14].y_lo
            // Fixed-column commitment 15, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0b80), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].x_hi
            mstore(add(payload, 0x0ba0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].x_lo
            mstore(add(payload, 0x0bc0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].y_hi
            mstore(add(payload, 0x0be0), 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[15].y_lo
            // Fixed-column commitment 16, stored as one
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0c00), 0x0000000000000000000000000000000014882c111f9ad75475439587af1a71ef) // fixed_comms[16].x_hi
            mstore(add(payload, 0x0c20), 0x7f8ad298e76c610f108edf6166bb87fb31164e6a88e75eabef4c08bae9166aa3) // fixed_comms[16].x_lo
            mstore(add(payload, 0x0c40), 0x0000000000000000000000000000000005f84911870ac0ef85a7e32e00335990) // fixed_comms[16].y_hi
            mstore(add(payload, 0x0c60), 0x1960d0511df70e34b4ddb9af9bf333aaf545ebc88891a7c53641989b86862bca) // fixed_comms[16].y_lo
            // Permutation commitment 0, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0c80), 0x000000000000000000000000000000000a66c92f14a465178b2a3989ca72fbff) // permutation_comms[0].x_hi
            mstore(add(payload, 0x0ca0), 0x9ee75d791d441234ee0c6bbed9beeffd26b6032f30a8003e714f3ccd4d48e9e5) // permutation_comms[0].x_lo
            mstore(add(payload, 0x0cc0), 0x00000000000000000000000000000000075882282911db509cefef45e9420d40) // permutation_comms[0].y_hi
            mstore(add(payload, 0x0ce0), 0x70145ebf84263aebc8bbf486279ff74818ac28ed936d7d426640486705123ab1) // permutation_comms[0].y_lo
            // Permutation commitment 1, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0d00), 0x00000000000000000000000000000000134458254e98bd97065c528220a99b6d) // permutation_comms[1].x_hi
            mstore(add(payload, 0x0d20), 0x1446cea690677cd79d52aac42c8e13b5b9af97539d0e6944e3d01d71532a068d) // permutation_comms[1].x_lo
            mstore(add(payload, 0x0d40), 0x00000000000000000000000000000000159669742d638e049865e0598261d9c4) // permutation_comms[1].y_hi
            mstore(add(payload, 0x0d60), 0xc1806eb8442940732540e4e8a95f301a24d8589d1916655afa0f9e1493080b87) // permutation_comms[1].y_lo
            // Permutation commitment 2, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0d80), 0x000000000000000000000000000000000c7d9c8250a1e6ae574b74c2f596c91c) // permutation_comms[2].x_hi
            mstore(add(payload, 0x0da0), 0xe1dfa554694e91b669ce4c35fdb271f9bd39c946901ab0e914f93006b4015d1c) // permutation_comms[2].x_lo
            mstore(add(payload, 0x0dc0), 0x000000000000000000000000000000000960e333da47af4f9876e12bec203b22) // permutation_comms[2].y_hi
            mstore(add(payload, 0x0de0), 0x38db335c8a9e859b8b8bd24c0492a934751279f7d6f0fc9915e1e079f3d7c609) // permutation_comms[2].y_lo
            // Permutation commitment 3, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0e00), 0x000000000000000000000000000000000b6d148698e34b5f83ec67762b67b3e2) // permutation_comms[3].x_hi
            mstore(add(payload, 0x0e20), 0x0b78d3a2d41419550ebd7209ea828945791bd6f123bd8bd3d32a2aefaf4b61cc) // permutation_comms[3].x_lo
            mstore(add(payload, 0x0e40), 0x000000000000000000000000000000001734e21c0972ac36e8baf131d7606204) // permutation_comms[3].y_hi
            mstore(add(payload, 0x0e60), 0x67f9218e1def4cda90a9e7ed0ecaa26d509d2a7ab6367265d2ffbfcf810e83ea) // permutation_comms[3].y_lo
            // Permutation commitment 4, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0e80), 0x0000000000000000000000000000000011e7cb7a6317cc32faf92f6c130069fc) // permutation_comms[4].x_hi
            mstore(add(payload, 0x0ea0), 0x69b6b14f4238b0d2e6701ed72944ff3d805065ac2b8d9e435964472d4f2fde44) // permutation_comms[4].x_lo
            mstore(add(payload, 0x0ec0), 0x000000000000000000000000000000000ae2bbfda130ad0c5880569298a93298) // permutation_comms[4].y_hi
            mstore(add(payload, 0x0ee0), 0xd3f2337f3198d327c454d5efc6e5d66cda0381d551cb0f1272997b0307098407) // permutation_comms[4].y_lo
            // Permutation commitment 5, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0f00), 0x000000000000000000000000000000000024dc7a9ffe5a0ad89fac6bc7043335) // permutation_comms[5].x_hi
            mstore(add(payload, 0x0f20), 0x4df357d3f43cb246df9f6d9842310373db77665bd9f6537b91816a149496289a) // permutation_comms[5].x_lo
            mstore(add(payload, 0x0f40), 0x0000000000000000000000000000000014233de6c1924a8b3f25f5932fcbc004) // permutation_comms[5].y_hi
            mstore(add(payload, 0x0f60), 0x752a484f481d9020fe48a67bbee01cdbc5dbf1bd3a5fad05bf756bb7a4aea318) // permutation_comms[5].y_lo
            // Permutation commitment 6, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x0f80), 0x0000000000000000000000000000000019508b48fdb2975eb118421b6a190674) // permutation_comms[6].x_hi
            mstore(add(payload, 0x0fa0), 0x6abfee37a2564e1467c236d58174d40a090900bdcb6103b0d9709c55193eaf76) // permutation_comms[6].x_lo
            mstore(add(payload, 0x0fc0), 0x0000000000000000000000000000000003e7d72102d8042da5445b802352e37d) // permutation_comms[6].y_hi
            mstore(add(payload, 0x0fe0), 0x6f49027a39ba2a781eed399a95b4987c9dd7703e79bafe4de4ff43325b771139) // permutation_comms[6].y_lo
            // Permutation commitment 7, also a 4-word
            // EIP-2537 padded uncompressed G1 slot.
            mstore(add(payload, 0x1000), 0x0000000000000000000000000000000005dc8f2b72ae777521b247a2d2a64b6d) // permutation_comms[7].x_hi
            mstore(add(payload, 0x1020), 0x83e3ec2b89bb0e9da7f3fdf1774a48f682ac609ef8e90b82dad0d9f71866f927) // permutation_comms[7].x_lo
            mstore(add(payload, 0x1040), 0x00000000000000000000000000000000099ce0320e05f9e86da177c477603c59) // permutation_comms[7].y_hi
            mstore(add(payload, 0x1060), 0xf3eaac37a42b31054181b69421b9a3a60c151223ca80ba849789469483b1ad22) // permutation_comms[7].y_lo

            // Return exactly the INVALID prefix plus the generated payload. The
            // linked verifier pins this byte length and the resulting codehash.
            return(runtime, 0x1081)
        }
    }
}